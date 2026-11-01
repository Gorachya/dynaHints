use ark_bls12_381::{Bls12_381, Fr};
use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{Field, PrimeField, UniformRand, Zero};
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Evaluations, Polynomial,
    Radix2EvaluationDomain,
};
use ark_serialize::CanonicalSerialize;
use ark_std::{ops::*, test_rng};
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use sha2::{Digest, Sha256};
use std::time::Instant;

#[path = "../src/kzg.rs"]
mod kzg;
#[path = "../src/utils.rs"]
mod utils;

type Curve = Bls12_381;
type Kzg = kzg::KZG10<Curve, DensePolynomial<Fr>>;
type Params = kzg::UniversalParams<Curve>;
type G1 = <Curve as Pairing>::G1Affine;
type G2 = <Curve as Pairing>::G2Affine;

#[allow(dead_code)]
struct SyntheticProof {
    agg_pk: G1,
    agg_sigma: G2,
    agg_weight: Fr,
    committee_commitment: G1,
    parsum_signer_at_r_div_omega: Fr,
    parsum_sub_at_r_div_omega: Fr,
    opening_proof_at_r_div_omega: G1,
    parsum_signer_at_r: Fr,
    w_at_r: Fr,
    signer_bitmap_at_r: Fr,
    signer_quotient_at_r: Fr,
    parsum_sub_at_r: Fr,
    subset_weight_at_r: Fr,
    subset_quotient_at_r: Fr,
    subset_bitmap_at_r: Fr,
    opening_proof_at_r: G1,
    parsum_signer_commitment: G1,
    signer_bitmap_commitment: G1,
    signer_quotient_commitment: G1,
    parsum_sub_commitment: G1,
    subset_bitmap_commitment: G1,
    subset_quotient_commitment: G1,
    qz_commitment: G1,
    qx_commitment: G1,
    qx_mul_tau_commitment: G1,
}

struct SyntheticInputs {
    n: usize,
    committee_size: usize,
    threshold: usize,
    params: Params,
    signer_bitmap: Vec<Fr>,
    committee_bitmap: Vec<Fr>,
    weights: Vec<Fr>,
    pks: Vec<G1>,
    qz_terms: Vec<G1>,
    qx_terms: Vec<G1>,
    qx_mul_tau_terms: Vec<G1>,
    signatures: Vec<G2>,
    sk_commitment: G2,
    w_commitment: G1,
}

impl SyntheticInputs {
    fn new(
        n: usize,
        committee_size: usize,
        params: Params,
        rng: &mut impl ark_std::rand::RngCore,
    ) -> Self {
        let parties = n - 1;
        assert!(committee_size <= parties);
        let threshold = (committee_size / 2).max(1);

        let mut signer_bitmap = vec![Fr::zero(); parties];
        let mut committee_bitmap = vec![Fr::zero(); parties];
        for i in 0..committee_size {
            committee_bitmap[i] = Fr::from(1u64);
        }
        for i in 0..threshold {
            signer_bitmap[i] = Fr::from(1u64);
        }

        let weights = vec![Fr::from(1u64); parties];
        let mut pks: Vec<G1> = (0..n).map(|_| G1::rand(&mut *rng)).collect();
        let mut qz_terms: Vec<G1> = (0..n).map(|_| G1::rand(&mut *rng)).collect();
        let mut qx_terms: Vec<G1> = (0..n).map(|_| G1::rand(&mut *rng)).collect();
        let mut qx_mul_tau_terms: Vec<G1> = (0..n).map(|_| G1::rand(&mut *rng)).collect();
        pks[n - 1] = G1::zero();
        qz_terms[n - 1] = G1::zero();
        qx_terms[n - 1] = G1::zero();
        qx_mul_tau_terms[n - 1] = G1::zero();
        let signatures: Vec<G2> = (0..threshold).map(|_| G2::rand(&mut *rng)).collect();

        let w_poly = utils::interpolate_poly_over_mult_subgroup(&{
            let mut values = weights.clone();
            values.push(Fr::zero());
            values
        });
        let w_commitment = Kzg::commit_g1(&params, &w_poly).expect("weight commitment failed");
        Self {
            n,
            committee_size,
            threshold,
            params,
            signer_bitmap,
            committee_bitmap,
            weights,
            pks,
            qz_terms,
            qx_terms,
            qx_mul_tau_terms,
            signatures,
            sk_commitment: G2::rand(rng),
            w_commitment,
        }
    }
}

fn interpolate(values: &[Fr]) -> DensePolynomial<Fr> {
    let domain = Radix2EvaluationDomain::<Fr>::new(values.len()).expect("N must be a power of two");
    Evaluations::from_vec_and_domain(values.to_vec(), domain).interpolate()
}

fn combine_polynomials(terms: &[(&DensePolynomial<Fr>, Fr)]) -> DensePolynomial<Fr> {
    let max_len = terms
        .iter()
        .map(|(poly, _)| poly.coeffs.len())
        .max()
        .unwrap_or(1);
    let mut coeffs = vec![Fr::zero(); max_len];
    for (poly, scalar) in terms {
        for (i, coeff) in poly.coeffs.iter().enumerate() {
            coeffs[i] += *coeff * scalar;
        }
    }
    DensePolynomial::from_coefficients_vec(coeffs)
}

fn random_oracle(elements: &[Vec<u8>]) -> Fr {
    let mut hash = Sha256::new();
    for element in elements {
        hash.update(element);
    }
    let mut digest = hash.finalize();
    digest[31] = 0;
    Fr::from_le_bytes_mod_order(&digest)
}

fn point_bytes<T: CanonicalSerialize>(point: &T) -> Vec<u8> {
    let mut bytes = Vec::new();
    point
        .serialize_compressed(&mut bytes)
        .expect("serialization failed");
    bytes
}

fn filter_and_add(params: &Params, elements: &[G1], bitmap: &[Fr]) -> G1 {
    let zero_poly = utils::compute_constant_poly(&Fr::zero());
    let mut result = Kzg::commit_g1(params, &zero_poly).expect("zero commitment failed");
    for (element, active) in elements.iter().zip(bitmap) {
        if *active == Fr::from(1u64) {
            result = (result.into_group() + element).into_affine();
        }
    }
    result
}

fn divide_by_vanishing_polynomial(
    polynomial: &DensePolynomial<Fr>,
    n: usize,
) -> DensePolynomial<Fr> {
    let domain = Radix2EvaluationDomain::<Fr>::new(n).expect("N must be a power of two");
    let (quotient, remainder) = polynomial
        .divide_by_vanishing_poly(domain)
        .expect("vanishing polynomial division failed");
    debug_assert!(remainder.is_zero(), "polynomial is not divisible by X^N - 1");
    quotient
}

fn run_synthetic_prove(input: &SyntheticInputs) -> SyntheticProof {
    let n = input.n;
    let mut weights = input.weights.clone();
    let active_weight = input
        .signer_bitmap
        .iter()
        .zip(&weights)
        .fold(Fr::zero(), |sum, (b, w)| sum + (*b * w));
    weights.push(-active_weight);

    let mut signer_bitmap = input.signer_bitmap.clone();
    let mut committee_bitmap = input.committee_bitmap.clone();
    let subset_bitmap: Vec<Fr> = committee_bitmap
        .iter()
        .zip(&signer_bitmap)
        .map(|(committee, signer)| {
            if committee != signer {
                *committee + signer
            } else {
                Fr::zero()
            }
        })
        .collect();
    let mut subset_bitmap = subset_bitmap;
    let mut subset_weights = input.weights.clone();
    subset_weights.push(-Fr::from((input.committee_size - input.threshold) as u64));
    signer_bitmap.push(Fr::from(1u64));
    committee_bitmap.push(Fr::from(1u64));
    subset_bitmap.push(Fr::from(1u64));

    let inv_n = Fr::from(n as u64).inverse().expect("N must be nonzero");
    let mut signature_points = Vec::with_capacity(input.signatures.len());
    let mut signature_scalars = Vec::with_capacity(input.signatures.len());
    for signature in &input.signatures {
        signature_points.push(*signature);
        signature_scalars.push(inv_n);
    }
    let aggregated_signature =
        <<Curve as Pairing>::G2 as VariableBaseMSM>::msm(&signature_points, &signature_scalars)
            .expect("signature aggregation MSM failed")
            .into_affine();
    let public_key_scalars: Vec<Fr> = signer_bitmap
        .iter()
        .map(|active| {
            if *active == Fr::from(1u64) {
                inv_n
            } else {
                Fr::zero()
            }
        })
        .collect();
    let aggregated_public_key =
        <<Curve as Pairing>::G1 as VariableBaseMSM>::msm(&input.pks, &public_key_scalars)
            .expect("public-key aggregation MSM failed")
            .into_affine();

    let domain = Radix2EvaluationDomain::<Fr>::new(n).expect("N must be a power of two");
    let omega_inv = domain
        .group_gen
        .inverse()
        .expect("domain generator is nonzero");
    let lagrange_last = utils::lagrange_poly(n, n - 1);
    let w_poly = interpolate(&weights);
    let signer_poly = interpolate(&signer_bitmap);
    let subset_poly = interpolate(&subset_bitmap);
    let signer_prefix = prefix_weight_polynomial(&weights, &signer_bitmap);
    let subset_prefix = prefix_weight_polynomial(&subset_weights, &subset_bitmap);
    let signer_prefix_shifted = utils::poly_domain_mult_ω(&signer_prefix, &omega_inv);
    let subset_prefix_shifted = utils::poly_domain_mult_ω(&subset_prefix, &omega_inv);
    let subset_weight_poly = interpolate(&subset_weights);

    let signer_q1 = divide_by_vanishing_polynomial(
        &signer_prefix
            .sub(&signer_prefix_shifted)
            .sub(&w_poly.mul(&signer_poly)),
        n,
    );
    let signer_q2 =
        divide_by_vanishing_polynomial(&lagrange_last.mul(&signer_prefix), n);
    let signer_q3 = divide_by_vanishing_polynomial(
        &signer_poly.mul(&signer_poly).sub(&signer_poly),
        n,
    );
    let signer_q4 = divide_by_vanishing_polynomial(
        &lagrange_last
            .clone()
            .mul(&signer_poly.sub(&utils::compute_constant_poly(&Fr::from(1u64)))),
        n,
    );

    let subset_q1 = divide_by_vanishing_polynomial(
        &subset_prefix
            .sub(&subset_prefix_shifted)
            .sub(&subset_weight_poly.mul(&subset_poly)),
        n,
    );
    let subset_q2 =
        divide_by_vanishing_polynomial(&lagrange_last.mul(&subset_prefix), n);
    let subset_q3 = divide_by_vanishing_polynomial(
        &subset_poly.mul(&subset_poly).sub(&subset_poly),
        n,
    );
    let subset_q4 = divide_by_vanishing_polynomial(
        &utils::lagrange_poly(n, n - 1)
            .mul(&subset_poly.sub(&utils::compute_constant_poly(&Fr::from(1u64)))),
        n,
    );

    let commitments = &input.params;
    let parsum_signer_commitment =
        Kzg::commit_g1(commitments, &signer_prefix).expect("signer prefix commitment failed");
    let signer_bitmap_commitment =
        Kzg::commit_g1(commitments, &signer_poly).expect("signer bitmap commitment failed");
    let parsum_sub_commitment =
        Kzg::commit_g1(commitments, &subset_prefix).expect("subset prefix commitment failed");
    let subset_bitmap_commitment =
        Kzg::commit_g1(commitments, &subset_poly).expect("subset bitmap commitment failed");
    let committee_commitment = <<Curve as Pairing>::G1 as VariableBaseMSM>::msm(
        &commitments.powers_of_g[..n],
        &committee_bitmap,
    )
    .expect("committee commitment MSM failed")
    .into_affine();

    let qz = filter_and_add(commitments, &input.qz_terms, &signer_bitmap);
    let qx = filter_and_add(commitments, &input.qx_terms, &signer_bitmap);
    let qx_mul_tau = filter_and_add(commitments, &input.qx_mul_tau_terms, &signer_bitmap);
    let v = random_oracle(&[
        point_bytes(&input.sk_commitment),
        point_bytes(&input.w_commitment),
        point_bytes(&signer_bitmap_commitment),
        point_bytes(&parsum_signer_commitment),
        point_bytes(&qx),
        point_bytes(&qz),
        point_bytes(&qx_mul_tau),
    ]);
    let v2 = v * v;
    let v4 = v2 * v2;
    let v8 = v4 * v4;
    let signer_q = combine_polynomials(&[
        (&signer_q1, Fr::from(1u64)),
        (&signer_q3, v),
        (&signer_q2, v2),
        (&signer_q4, v4),
    ]);
    let subset_q = combine_polynomials(&[
        (&subset_q1, Fr::from(1u64)),
        (&subset_q3, v2),
        (&subset_q2, v4),
        (&subset_q4, v8),
    ]);
    let signer_quotient_commitment =
        Kzg::commit_g1(commitments, &signer_q).expect("signer quotient commitment failed");
    let subset_quotient_commitment =
        Kzg::commit_g1(commitments, &subset_q).expect("subset quotient commitment failed");

    let r = random_oracle(&[
        point_bytes(&input.sk_commitment),
        point_bytes(&input.w_commitment),
        point_bytes(&signer_bitmap_commitment),
        point_bytes(&parsum_signer_commitment),
        point_bytes(&qx),
        point_bytes(&qz),
        point_bytes(&qx_mul_tau),
        point_bytes(&signer_quotient_commitment),
        point_bytes(&subset_quotient_commitment),
    ]);
    let r_div_omega = r * omega_inv;
    let openings = [
        &signer_prefix,
        &w_poly,
        &signer_poly,
        &signer_q,
        &subset_prefix,
        &subset_weight_poly,
        &subset_poly,
        &subset_q,
    ];
    let mut opening_proofs = Vec::with_capacity(openings.len());
    for polynomial in openings {
        opening_proofs.push(
            Kzg::compute_opening_proof(commitments, polynomial, &r)
                .expect("opening proof at r failed"),
        );
    }
    let subset_prefix_at_r_div_omega =
        Kzg::compute_opening_proof(commitments, &subset_prefix, &r_div_omega)
            .expect("subset opening proof at r/omega failed");
    let signer_prefix_at_r_div_omega =
        Kzg::compute_opening_proof(commitments, &signer_prefix, &r_div_omega)
            .expect("signer opening proof at r/omega failed");

    let r_powers: Vec<Fr> = (0..8)
        .scan(Fr::from(1u64), |power, _| {
            let current = *power;
            *power *= r;
            Some(current)
        })
        .collect();
    let merged_opening = opening_proofs
        .iter()
        .zip(&r_powers)
        .fold(G1::zero(), |sum, (proof, scalar)| {
            (sum.into_group() + proof.mul(*scalar)).into_affine()
        });
    let merged_opening_at_r_div_omega = (subset_prefix_at_r_div_omega.into_group()
        + signer_prefix_at_r_div_omega.mul(r_div_omega))
    .into_affine();

    SyntheticProof {
        agg_pk: aggregated_public_key,
        agg_sigma: aggregated_signature,
        agg_weight: active_weight,
        committee_commitment,
        parsum_signer_at_r_div_omega: signer_prefix.evaluate(&r_div_omega),
        parsum_sub_at_r_div_omega: subset_prefix.evaluate(&r_div_omega),
        opening_proof_at_r_div_omega: merged_opening_at_r_div_omega,
        parsum_signer_at_r: signer_prefix.evaluate(&r),
        w_at_r: w_poly.evaluate(&r),
        signer_bitmap_at_r: signer_poly.evaluate(&r),
        signer_quotient_at_r: signer_q.evaluate(&r),
        parsum_sub_at_r: subset_prefix.evaluate(&r),
        subset_weight_at_r: subset_weight_poly.evaluate(&r),
        subset_quotient_at_r: subset_q.evaluate(&r),
        subset_bitmap_at_r: subset_poly.evaluate(&r),
        opening_proof_at_r: merged_opening,
        parsum_signer_commitment,
        signer_bitmap_commitment,
        signer_quotient_commitment,
        parsum_sub_commitment,
        subset_bitmap_commitment,
        subset_quotient_commitment,
        qz_commitment: qz,
        qx_commitment: qx,
        qx_mul_tau_commitment: qx_mul_tau,
    }
}

fn prefix_weight_polynomial(weights: &[Fr], bitmap: &[Fr]) -> DensePolynomial<Fr> {
    let mut sum = Fr::zero();
    let evaluations: Vec<Fr> = weights
        .iter()
        .zip(bitmap)
        .map(|(weight, active)| {
            sum += *weight * active;
            sum
        })
        .collect();
    interpolate(&evaluations)
}

#[allow(dead_code)]
fn benchmark_synthetic_prove(c: &mut Criterion) {
    let mut group = c.benchmark_group("synthetic_signature_aggregation_and_prove");
    group.sample_size(10);
    let fast_mode = std::env::var("DYNAHINTS_BENCH_MODE")
        .map(|mode| mode.eq_ignore_ascii_case("fast"))
        .unwrap_or(false);
    let n_exponent_max = if fast_mode { 14 } else { 20 };
    for n_exponent in (8usize..=n_exponent_max).step_by(2) {
        let n = 1usize << n_exponent;
        let mut rng = test_rng();
        let params = Kzg::setup(n, &mut rng).expect("KZG setup failed");

        for c_exponent in (6usize..=std::cmp::min(12, n_exponent - 2)).step_by(2) {
            let committee_size = 1usize << c_exponent;
            let input = SyntheticInputs::new(n, committee_size, params.clone(), &mut rng);
            let benchmark_id =
                BenchmarkId::new(format!("N_{n}_c_exp_{c_exponent}"), committee_size);
            group.bench_with_input(benchmark_id, &input, |b, input| {
                b.iter(|| black_box(run_synthetic_prove(black_box(input))));
            });
        }
    }
    group.finish();
}

criterion_group!(benches, benchmark_synthetic_prove);
criterion_main!(benches);
