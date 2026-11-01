//need to implement hint generation by all the parties and write it in a file 
#![allow(unused_imports)]
use std::time::Instant;
use std::sync::Arc;
//use serde::{Serialize, Deserialize,};
use std::fs::File;
use std::io::{self, BufWriter, Write, BufReader, Read};
//use std::io::{self, BufReader, BufWriter, Write, Seek, SeekFrom, Read};
use ark_serialize::{CanonicalSerialize, SerializationError, CanonicalDeserialize, Compress, Valid, Validate};
use ark_ff::{Field, biginteger::BigInteger256};
use ark_poly::{
    Polynomial,
    univariate::DensePolynomial, 
    EvaluationDomain, 
    Radix2EvaluationDomain,
    Evaluations
};
//use ark_std::rand::Rng;
use ark_std::{UniformRand, test_rng, ops::*};
use ark_bls12_381::Bls12_381;
use ark_ec::{pairing::Pairing, CurveGroup};
use ark_ec::VariableBaseMSM;

//use _bls_signature as bls;
//use pippengerTesting::* ;
use crate::kzg::*;
use crate::utils ;


type Curve = Bls12_381;
type KZG = KZG10::<Curve, DensePolynomial<<Curve as Pairing>::ScalarField>>;
type F = ark_bls12_381::Fr;
type G1 = <Curve as Pairing>::G1Affine;
type G2 = <Curve as Pairing>::G2Affine;

#[derive(CanonicalSerialize, CanonicalDeserialize,Clone,Debug, PartialEq, Eq)]
//#[derive(Serialize, Deserialize, Debug)]
pub struct Hint {
    /// index in the address book
    i: usize,
    /// public key pk = [sk]_1
    pk_i: G1,
    /// [ sk_i L_i(τ) ]_1
    sk_i_l_i_of_tau_com_1: G1,
    /// [ sk_i L_i(τ) ]_2
    sk_i_l_i_of_tau_com_2: G2,
    /// qz_i_terms[i] = [ sk_i * ((L_i^2(τ) - L_i(τ)) / Z(τ)) ]_1
    /// \forall j != i, qz_i_terms[j] = [ sk_i * (L_i(τ) * L_j(τ) / Z(τ)) ]_1
    qz_i_terms: Vec<G1>,
    /// [ sk_i ((L_i(τ) - L_i(0)) / τ ]_1
    qx_i_term: G1,
    /// [ sk_i ((L_i(τ) - L_i(0))]_1
    qx_i_term_mul_tau: G1,
}
#[allow(dead_code)]

pub fn hint_gen(
    params: &UniversalParams<Curve>,
    n: usize, 
    i: usize, 
    sk_i: &F) -> Hint {
    //let us compute the q1 term
    let l_i_of_x = utils::lagrange_poly(n, i);
    let mut qz_terms = vec![];
    //let us compute the cross terms of q1
    for j in 0..n {
        let num: DensePolynomial<F>;// = compute_constant_poly(&F::from(0));
        if i == j {
            num = l_i_of_x.clone().mul(&l_i_of_x).sub(&l_i_of_x);
        } else { //cross-terms
            let l_j_of_x = utils::lagrange_poly(n, j);
            num = l_j_of_x.mul(&l_i_of_x);
        }

        let f = utils::divide_by_vanishing_polynomial(&num, n);
        let sk_times_f = utils::poly_eval_mult_c(&f, &sk_i);

        let com = KZG::commit_g1(&params, &sk_times_f)
            .expect("commitment failed");

        qz_terms.push(com);
    }

    let x_monomial = utils::compute_x_monomial();
    let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
    let l_i_of_0_poly = utils::compute_constant_poly(&l_i_of_0);

    //numerator is l_i(x) - l_i(0)
    let num = l_i_of_x.sub(&l_i_of_0_poly);
    //denominator is x
    let den = x_monomial.clone();
    //qx_term = sk_i * (l_i(x) - l_i(0)) / x
    let qx_term = utils::poly_eval_mult_c(&num.div(&den), &sk_i);
    //qx_term_mul_tau = sk_i * (l_i(x) - l_i(0)) / x
    let qx_term_mul_tau = utils::poly_eval_mult_c(&num, &sk_i);
    //qx_term_com = [ sk_i * (l_i(τ) - l_i(0)) / τ ]_1
    let qx_term_com = KZG::commit_g1(&params, &qx_term).expect("commitment failed");
    //qx_term_mul_tau_com = [ sk_i * (l_i(τ) - l_i(0)) ]_1
    let qx_term_mul_tau_com = KZG::commit_g1(&params, &qx_term_mul_tau).expect("commitment failed");

    //release my public key
    let sk_as_poly = utils::compute_constant_poly(&sk_i);
    let pk = KZG::commit_g1(&params, &sk_as_poly).expect("commitment failed");
   

    let sk_times_l_i_of_x = utils::poly_eval_mult_c(&l_i_of_x, &sk_i);
    let com_sk_l_i_g1 = KZG::commit_g1(&params, &sk_times_l_i_of_x).expect("commitment failed");
    let com_sk_l_i_g2 = KZG::commit_g2(&params, &sk_times_l_i_of_x).expect("commitment failed");

    Hint {
        i: i,
        pk_i: pk,
        sk_i_l_i_of_tau_com_1: com_sk_l_i_g1,
        sk_i_l_i_of_tau_com_2: com_sk_l_i_g2,
        qz_i_terms: qz_terms,
        qx_i_term: qx_term_com,
        qx_i_term_mul_tau: qx_term_mul_tau_com,
    }
}
#[allow(dead_code)]
pub fn sample_secret_keys(num_parties: usize) -> Vec<F> {
    let mut rng = test_rng();
    let mut keys = vec![];
    for _ in 0..num_parties {
        keys.push(F::rand(&mut rng));
    }
    keys
}

#[allow(dead_code)]
pub fn generate_hints_and_write (
    params: &UniversalParams<Curve>,
    n: usize,  
    sk: Vec<F>,
    path: &str,
    ) -> Result<(), SerializationError> {
        let file = File::create(path).map_err(|e| SerializationError::IoError(e))?;
        let mut writer = BufWriter::new(file);
        //let params = Arc::new(params) ;

        (n as u64).serialize_uncompressed(&mut writer)?;
    
            for i in 0..n {
                let hint = hint_gen(params, n, i, &sk[i]);
                hint.i.serialize_uncompressed(&mut writer)?;
                hint.pk_i.serialize_uncompressed(&mut writer)?;
                hint.sk_i_l_i_of_tau_com_1.serialize_uncompressed(&mut writer)?;
                hint.sk_i_l_i_of_tau_com_2.serialize_uncompressed(&mut writer)?;
    
                // Serialize `qz_i_terms` vector length and elements
                (hint.qz_i_terms.len() as u64).serialize_uncompressed(&mut writer)?;
                for term in &hint.qz_i_terms {
                    term.serialize_uncompressed(&mut writer)?;
                }
    
                hint.qx_i_term.serialize_uncompressed(&mut writer)?;
                hint.qx_i_term_mul_tau.serialize_uncompressed(&mut writer)?;

            }
            writer.flush()?;

        Ok(())

    }
 #[allow(dead_code)]
  pub fn write_secret_keys(n: usize, path: &str) -> Result<(), SerializationError> {
        let mut file = File::create(path).map_err(|e| SerializationError::IoError(e))?;
        let mut sk: Vec<F> = sample_secret_keys(n - 1);
        sk.push(F::from(0));
        //let rng = &mut test_rng();
        

        (sk.len() as u64).serialize_uncompressed(&mut file)?;

        for i in 0..sk.len() {
            sk[i].serialize_uncompressed(&mut file)? ;
        }
        Ok(())
    
    }

    pub fn read_secret_keys(path: &str) ->  Result<Vec<F>, SerializationError> {
        let mut file = File::open(path).map_err(SerializationError::IoError)?;
       
      
    

        let sk_count = u64::deserialize_uncompressed(&mut file)? as usize;
        let mut sk:Vec<F> = Vec::with_capacity(sk_count);
    
        // Deserialize each field from the file
        for _ in 0..sk_count {
            let sk_i = F::deserialize_uncompressed(&mut file)?;
    
        sk.push(sk_i) ;
    }
    Ok(sk)
}

#[test]
fn test_hint_gen_time_for_1024() {
    let n = 1024;
    let rng = &mut test_rng();
    let params = KZG::setup(n,rng).expect("setup failed") ;
    let sk = sample_secret_keys(1) ;
    let start = Instant::now();
    let _hint = hint_gen(&params, n, 0, &sk[0]) ;
    let duration = start.elapsed() ;
    println!("time to generate one hint is {:?}",duration);
}
#[test]
fn test_hint_gen_time_for_2048() {
    let n = 2048;
    let rng = &mut test_rng();
    let params = KZG::setup(n,rng).expect("setup failed") ;
    let sk = sample_secret_keys(1) ;
    let start = Instant::now();
    let _hint = hint_gen(&params, n, 0, &sk[0]) ;
    let duration = start.elapsed() ;
    println!("time to generate one hint is {:?}",duration);
}