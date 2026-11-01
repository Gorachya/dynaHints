//use std::ptr::metadata;
#![allow(unused_imports)]
use std::time::{Duration, Instant};
use std::sync::Arc;
//use serde::{Serialize, Deserialize,};
use std::fs::File;
use std::io::{self, BufReader, BufWriter, Seek, SeekFrom, Write, Read};
use std::vec;
use std::env;
use rayon::prelude::*;
use tracing_subscriber::util;
use std::error::Error;

//use pprof::ProfilerGuard;

//use rand::SeedableRng;
use sha2::{Digest, Sha256};
use hex ;
use std::collections::HashSet;

use vrf::openssl::{CipherSuite, ECVRF};
use vrf::VRF;

//use rand_chacha ;

use aes::Aes128;
use aes::cipher::{BlockEncrypt, KeyInit,
    generic_array::GenericArray,
};

use ark_serialize::{CanonicalSerialize, SerializationError, CanonicalDeserialize, Compress, Valid, Validate};
use ark_ff::{Field, Zero, biginteger::BigInteger256};
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

use _bls_signature as bls;
//use pippengerTesting::* ;

//use w3f_bls::{Keypair,ZBLS,Message,Signed};

use kzg::*;

mod utils;
mod kzg;
mod hintgen;
mod _bls_signature;
//mod pippengerTesting;

type Curve = Bls12_381;
type KZG = KZG10::<Curve, DensePolynomial<<Curve as Pairing>::ScalarField>>;
type F = ark_bls12_381::Fr;
type G1 = <Curve as Pairing>::G1Affine;
type G2 = <Curve as Pairing>::G2Affine;

///partial bls signature structure 
#[allow(dead_code)]
struct PartialSig {
    sigma: G2,
    i: usize,
}
struct PartialSigDleq {
    sigma: G2,
    c: F,
    s: F,
    i: usize,
}

/// hinTS proof structure
struct Proof {
    /// aggregate public key (aPK_signer in the paper)
    agg_pk: G1,
    ///aggregated signature
    agg_sigma: G2,
    /// aggregate weight (w in the paper)
    agg_weight: F,
    ///..................//
    /// commitments regarding committee
    b_committee_of_tau: G1,
    ///.....................///
    /// commitments regarding signers 
    /// commitment to the bitmap polynomial ([B(τ)]_1 in the paper)
    b_signer_of_tau: G1,
    /// commitment to the Q_x polynomial ([Q_x(τ)]_1 in the paper)
    qx_of_tau_signer: G1,
    /// commitment to the Q_x polynomial ([Q_x(τ) . τ ]_1 in the paper)
    qx_of_tau_mul_tau_signer: G1,
    /// commitment to the Q_z polynomial ([Q_z(τ)]_1 in the paper)
    qz_of_tau_signer: G1,
    ///.....................///
    b_sub_of_tau: G1,
    /// commitment to the ParSum_sub
    parsum_sub_of_tau_com: G1,
     //batching 
     q_sub_of_tau_com: G1,
    /// commitment to the ParSum_signer polynomial ([ParSum(τ)]_1 in the paper)
    parsum_signer_of_tau_com: G1,
    ///batching 
    q_of_tau_com: G1,

    /// merged opening proof for all openings at x = r
    opening_proof_r: G1,
    /// proof for the ParSum opening at x = r / ω
    opening_proof_r_div_ω: G1,

    /// polynomial evaluation of ParSum(x) at x = r
    parsum_signer_of_r: F,
    /// polynomial evaluation of ParSum(x) at x = r / ω
    parsum_signer_of_r_div_ω: F,
    /// polynomial evaluation of W(x) at x = r
    w_of_r: F,
    /// polynomial evaluation of bitmap B(x) at x = r
    b_signer_of_r: F,
    q_of_r: F,

    /// polynomial evaluation of ParSum_sub(x) at x = r
    parsum_sub_of_r: F,
    /// polynomial evaluation of ParSum_sub(x) at x = r / ω
    parsum_sub_of_r_div_ω: F,
    /// polynomial evaluation of W_sub(x) at x = r
    w_sub_of_r: F,
    /// polynomial evaluation of bitmap B_sub(x) at x = r
    b_sub_of_r: F,
    q_sub_of_r: F,
}

/// Hint contains all material output by a party during the setup phase
#[allow(dead_code)]

#[derive(CanonicalSerialize, CanonicalDeserialize,Clone,Debug, PartialEq, Eq)]
//#[derive(Serialize, Deserialize, Debug)]
struct Hint {
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

#[derive(Clone,PartialEq, Eq, Debug,CanonicalSerialize, CanonicalDeserialize)]
struct PublicPolynomials {
    i: usize ,
    l_i_of_x: DensePolynomial<F>,
    //z_of_x: DensePolynomial<F>,
    cross_polynomials: Vec<DensePolynomial<F>>,
   // l_i_of_x_sub_l_i_of_tau : DensePolynomial<F>,
    l_i_of_zero_poly: DensePolynomial<F>,    

}

//hint independent one time setup computations
#[derive(CanonicalSerialize, CanonicalDeserialize,Clone,Debug, PartialEq, Eq)]
//public polynomial commitments to verify the hinTs
struct HintIndependentSetupElements {
    i: usize,
    l_i_of_tau_com_2: G2,
    qz_i_terms: Vec<G2>,
    qx_i_term: G2,
    qx_i_term_mul_tau: G2,

}

/// AggregationKey contains all material needed by Prover to produce a hinTS proof
struct AggregationKey {
    /// number of parties plus one (must be a power of 2)
    n: usize,
    c: usize,
    /// weights has all parties' weights, where weights[i] is party i's weight
    weights: Vec<F>,
    /// pks contains all parties' public keys, where pks[i] is g^sk_i
    pks: Vec<G1>,
    qz_terms : Vec<G1>,
    /// qx_terms contains pre-processed hints for the Q_x polynomial.
    /// qx_terms[i] has the form [ sk_i * (L_i(\tau) - L_i(0)) / x ]_1
    qx_terms : Vec<G1>,
    /// qx_mul_tau_terms contains pre-processed hints for the Q_x * x polynomial.
    /// qx_mul_tau_terms[i] has the form [ sk_i * (L_i(\tau) - L_i(0)) ]_1
    qx_mul_tau_terms : Vec<G1>,
}

struct VerificationKey {
    /// the universe has n - 1 parties (where n is a power of 2)
    n: usize,
    //the committee has c-1 parties 
    c : usize,
    /// first G1 element from the KZG CRS (for zeroth power of tau)
    g_0: G1,
    /// first G2 element from the KZG CRS (for zeroth power of tau)
    h_0: G2,
    /// second G1 element from the KZG CRS (for first power of tau)
    h_1: G2,
    /// commitment to the L_{n-1} polynomial
    l_n_minus_1_of_tau_com: G1,
    /// commitment to the W polynomial
    w_of_tau_com: G1,
    /// commitment to the SK polynomial
    sk_of_tau_com: G2,
    /// commitment to the vanishing polynomial Z(x) = x^n - 1
    z_of_tau_com: G2,
    /// commitment to the f(x) = x, which equals [\tau]_2
    tau_com: G2
}
//u64::rand(&mut rng)

//this will also work for random weights but we have only checked for equal weights 
//where weight of every party is taken 1
fn sample_weights(n: usize) -> Vec<F> {
    //let mut rng = &mut test_rng();
    //without weight setting
    (0..n).map(|_| F::from(1)).collect()
    //with weight setting
    //(0..n).map(|_| F::from(u64::rand(&mut rng))).collect()
}

//this is to create committee from the vrf output 

fn create_committee(com_size: usize, universe_size: usize, vrf_output: &Vec<u8>) -> Vec<F> {
    
 
     //putting the vrf output as key into aes
     let mut result = HashSet::new();
     let beta1 = &vrf_output.clone() ;
     let key:[u8;16] = [beta1[0],beta1[1],beta1[2],beta1[3],beta1[4],
                       beta1[5],beta1[6],beta1[7],beta1[8],beta1[9],
                       beta1[10],beta1[11],beta1[12],beta1[13],beta1[14],
                       beta1[15]] ;
 
                       
     let cipher = Aes128::new(&GenericArray::from_slice(&key));
     
 
     let mut counter: u128 = 0; // 128-bit counter
 
     while result.len() < com_size {
        //println!("result length {}",result.len()) ;
         let mut block = GenericArray::clone_from_slice(&counter.to_be_bytes());
         //println!("create committee block is {:?}",block) ;
         cipher.encrypt_block(&mut block);

         //convert the block in to 128 bit 
         let encrypted_value = u128::from_be_bytes(block.as_slice().try_into().expect("Incorrect length"));
         //map the encrypted value in the range of the universe size
         let random_number = (encrypted_value % (universe_size as u128)) as u128 ;
         result.insert(random_number as u32);
         counter += 1;
     }
     let comm: Vec<u32> = result.into_iter().collect() ;
    
     let mut bitmap_com = Vec::with_capacity(universe_size) ;
     for _i in 0..universe_size {
         bitmap_com.push(F::from(0)) ;
     }
     for &value in &comm {
         let temp = value as usize ;
         if temp < universe_size {
             bitmap_com[temp] = F::from(1) ;
         }    
     }
     bitmap_com
     
     
}

//creating random t no of signers
fn create_subset_bitmap(n: usize, bmap: &Vec<F>, thresh: usize)-> Vec<F> {
    let mut sub_map = Vec::with_capacity(n);
    let mut t = thresh.clone() ;
    //let rng = &mut test_rng() ;
    for i in 0..n {
        if bmap[i] == F::from(0) {
            sub_map.push(F::from(0)) ;

        }
        else {
            if t > 0 {
                sub_map.push(F::from(1));
                t = t-1 ;
            }
            else {
                sub_map.push(F::from(0)) ;
            }
           
        }

    }

    sub_map

}

fn verify_committee(com_size: usize, universe_size: usize, b_com_of_tau: G1,vrf_instan: &mut ECVRF,vrf_message: &[u8], vrf_proof: &Vec<u8>, vrf_pk: &Vec<u8>,params: &UniversalParams<Curve>) {

    let pi = vrf_proof.clone() ;
    let pk = vrf_pk.clone() ;
    //let start = Instant::now();
    
    let hash = vrf_instan.proof_to_hash(&pi).unwrap();
    //println!("verify committee hash is {:?}",hash) ;
    let beta = vrf_instan.verify(&pk, &pi, &vrf_message);
    match beta.as_ref() {
        Ok(beta) => {
            assert_eq!(&hash, beta);
        }
        Err(e) => {
            println!("VRF proof is not valid: {}", e);
        }
    }
    //let duration = start.elapsed();
    //println!("time to verify vrf proof is {:?}",duration);
    
   
    let mut result = HashSet::new();
   
     let beta1 = &beta.unwrap().clone() ;
     //let start = Instant::now() ;
     let key:[u8;16] = [beta1[0],beta1[1],beta1[2],beta1[3],beta1[4],
                       beta1[5],beta1[6],beta1[7],beta1[8],beta1[9],
                       beta1[10],beta1[11],beta1[12],beta1[13],beta1[14],
                       beta1[15]] ;
 
                       
     let cipher = Aes128::new(&GenericArray::from_slice(&key));
 
     let mut counter: u128 = 0; // 128-bit counter
 
     while result.len() < com_size {
         let mut block = GenericArray::clone_from_slice(&counter.to_be_bytes());
         //println!("verify committee block is {:?}",block) ;
         cipher.encrypt_block(&mut block);
         //convert the block in to 128 bit 
         let encrypted_value = u128::from_be_bytes(block.as_slice().try_into().expect("Incorrect length"));
         //println!("verify committee encrypted_value is {:?}",encrypted_value) ;
         //map the encrypted value in the range of the universe size
         let random_number = (encrypted_value % (universe_size as u128)) as u128 ;
         result.insert(random_number as u32);
         counter += 1;
     }
     let comm: Vec<u32> = result.into_iter().collect() ;
     
     //println!("The positions are {:?}",comm) ;
     let mut bitmap_com = Vec::with_capacity(universe_size) ;
     for _i in 0..universe_size {
         bitmap_com.push(F::from(0)) ;
     }
     for &value in &comm {
         let temp = value as usize ;
         if temp < universe_size {
             bitmap_com[temp] = F::from(1) ;
         }    
     }
     bitmap_com.push(F::from(1));

    
    
     let bitmap_com_of_tau = <<Curve as Pairing>::G1 as VariableBaseMSM>
    ::msm(&params.powers_of_g[0..universe_size+1], &bitmap_com).unwrap().into_affine() ;
    //let duration = start.elapsed() ;
    //println!("time to compute committee commitment is {:?}",duration) ;
     assert_eq!(bitmap_com_of_tau , b_com_of_tau) ;
    
}

//partial bls signature generation with discrete log proof
fn partial_signatures_gen_dleq(universe_size: usize, sk: &Vec<F>, bitmap_signer: &Vec<F>, message: &Vec<u8>, dst: &Vec<u8>, pks: &Vec<G1>,params: &UniversalParams<Curve>)-> Vec<PartialSigDleq> {
    let mut partial_sig_vec = vec![] ;
    for i in 0..universe_size {
        if bitmap_signer[i] == F::from(1) {
            let (sig, c, s) =  bls::bls_sign_with_dleq( message,sk[i], dst,params, pks[i]);
            let p_sig = PartialSigDleq {
                sigma:sig,
                c:c,
                s:s,
                i: i,
            } ;
            partial_sig_vec.push(p_sig) ;

        }

    }
    partial_sig_vec

}

//partial signature and the discrete log proof verification
fn partial_signatures_verification_dleq(partial_sig_vec: &Vec<PartialSigDleq>,message: &Vec<u8>,dst: &Vec<u8>,pks: &Vec<G1>,params: &UniversalParams<Curve>) {
    for j in 0..partial_sig_vec.len() {
        let p_sig = &partial_sig_vec[j] ; 
        bls::bls_verify_with_dleq(message, dst, pks[p_sig.i], params, p_sig.sigma, p_sig.c, p_sig.s);
    }

}

//generating the lagrange coefficients for hints verification
fn generate_public_polynomials(n: usize,i: usize, _z_of_x: &DensePolynomial<F>) -> PublicPolynomials {
    let l_i_of_x = utils::lagrange_poly(n, i);
    //let z_of_x = utils::compute_vanishing_poly(n);
    let mut cross_terms = vec![];
    for j in 0..n {
        let num: DensePolynomial<F>;// = compute_constant_poly(&F::from(0));
        if i == j {
            num = l_i_of_x.clone().mul(&l_i_of_x).sub(&l_i_of_x);
        } else { //cross-terms
            let l_j_of_x = utils::lagrange_poly(n, j);
            num = l_j_of_x.mul(&l_i_of_x);
        }
        cross_terms.push(divide_by_vanishing_polynomial(&num, n));
    }
   // let x_monomial = utils::compute_x_monomial();
    let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
    let l_i_of_0_poly = utils::compute_constant_poly(&l_i_of_0);
   // let num = l_i_of_x.sub(&l_i_of_0_poly);
   PublicPolynomials{
    i:i,
    l_i_of_x: l_i_of_x,
   // z_of_x: z_of_x,
    cross_polynomials: cross_terms,
    l_i_of_zero_poly: l_i_of_0_poly,
   }

    
}

//all the expensive computation can be implemented using multi threads
#[allow(dead_code)]
fn write_public_polynomials(public_polys: &Vec<PublicPolynomials>, path: &str) -> Result<(),SerializationError> {
    let mut file = File::create(path).map_err(|e| SerializationError::IoError(e))?;
    println!("Writing pps") ;
    for pp in public_polys {
        pp.i.serialize_uncompressed(&mut file)?;
        pp.l_i_of_x.serialize_uncompressed(&mut file)?;
        pp.l_i_of_zero_poly.serialize_uncompressed(&mut file)?;
       // pp.z_of_x.serialize_uncompressed(&mut file)?;

        // Serialize `qz_i_terms` vector length and elements
        (pp.cross_polynomials.len() as u64).serialize_uncompressed(&mut file)?;
        for term in &pp.cross_polynomials {
            term.serialize_uncompressed(&mut file)?;
        }
    }

    Ok(())


}

//multithreaded implementation 
 #[allow(dead_code)]

fn generate_public_polys_and_write (
    n: usize,  
    path: &str) -> Result<(), SerializationError> {
        let file = File::create(path).map_err(|e| SerializationError::IoError(e))?;
        let mut writer = BufWriter::new(file);
        let z_of_x = utils::compute_vanishing_poly(n);
        //let z_of_x = Arc::new(z_of_x);

        for i in 0..n {
            let pp = generate_public_polynomials(n, i, &z_of_x);
            pp.i.serialize_uncompressed(&mut writer)?;
            pp.l_i_of_x.serialize_uncompressed(&mut writer)?;
            pp.l_i_of_zero_poly.serialize_uncompressed(&mut writer)?;
            //pp.z_of_x.serialize_uncompressed(&mut file)?;

            // Serialize `qz_i_terms` vector length and elements
            (pp.cross_polynomials.len() as u64).serialize_uncompressed(&mut writer)?;
            for term in &pp.cross_polynomials {
                term.serialize_uncompressed(&mut writer)?;
            }

        }
        writer.flush()?;

        Ok(())

    }
#[allow(dead_code)]
fn read_public_poly_from_file(path: &str, n:usize) -> Result<Vec<PublicPolynomials>, SerializationError> {
    let mut file = File::open(path).map_err(SerializationError::IoError)?;
    

    let mut public_polys = Vec::with_capacity(n);
    //let len = u64::deserialize_uncompressed(&mut file)?;

    // Deserialize each field from the file
    for _ in 0..n {
        let i = usize::deserialize_uncompressed(&mut file)?;
        let l_i_of_x = DensePolynomial::deserialize_uncompressed(&mut file)?;
        let l_i_of_zero_poly = DensePolynomial::deserialize_uncompressed(&mut file)?;
        //let z_of_x = DensePolynomial::deserialize_uncompressed(&mut file)?;
    let cross_terms_len = u64::deserialize_uncompressed(&mut file)? as usize;
    let mut cross_polynomials = Vec::with_capacity(cross_terms_len);
    for _ in 0..cross_terms_len {
        cross_polynomials.push(DensePolynomial::deserialize_uncompressed(&mut file)?);
    }

    public_polys.push(PublicPolynomials{
        i,
        l_i_of_x,
        //z_of_x,
        cross_polynomials,
        l_i_of_zero_poly
    })
}
Ok(public_polys)

 }

 //multithreaded implementation 
#[allow(dead_code)]
fn write_hints_to_file(hints: &Vec<Hint>, path: &str, _n:usize) -> Result<(), SerializationError> {
    //let mut file = File::create(path).map_err(|_| SerializationError::IoError) ;
   //let mut file = BufReader::new(File::open(path).map_err(SerializationError::IoError)?);
    let mut file = File::create(path).map_err(|e| SerializationError::IoError(e))?;

       println!("Writing hints") ;
        (hints.len() as u64).serialize_uncompressed(&mut file)?;

        // Serialize each `Hint` in the vector
        for hint in hints {
            hint.i.serialize_uncompressed(&mut file)?;
            hint.pk_i.serialize_uncompressed(&mut file)?;
            hint.sk_i_l_i_of_tau_com_1.serialize_uncompressed(&mut file)?;
            hint.sk_i_l_i_of_tau_com_2.serialize_uncompressed(&mut file)?;

            // Serialize `qz_i_terms` vector length and elements
            (hint.qz_i_terms.len() as u64).serialize_uncompressed(&mut file)?;
            for term in &hint.qz_i_terms {
                term.serialize_uncompressed(&mut file)?;
            }

            hint.qx_i_term.serialize_uncompressed(&mut file)?;
            hint.qx_i_term_mul_tau.serialize_uncompressed(&mut file)?;
        }

        Ok(())
    }


//multithreaded implementation 
fn read_hints_from_file(path: &str) -> Result<Vec<Hint>, SerializationError> {
    let mut file = File::open(path).map_err(SerializationError::IoError)?;
    

    let hint_count = u64::deserialize_uncompressed(&mut file)? as usize;
    let mut hints = Vec::with_capacity(hint_count);

    // Deserialize each field from the file
    for _ in 0..hint_count {
        let i = usize::deserialize_uncompressed(&mut file)?;
    let pk_i = G1::deserialize_uncompressed(&mut file)?;
    let sk_i_l_i_of_tau_com_1 = G1::deserialize_uncompressed(&mut file)?;
    let sk_i_l_i_of_tau_com_2 = G2::deserialize_uncompressed(&mut file)?;

    // Deserialize the length of `qz_i_terms` and then each element
    let qz_i_terms_len = u64::deserialize_uncompressed(&mut file)? as usize;
    let mut qz_i_terms = Vec::with_capacity(qz_i_terms_len);
    for _ in 0..qz_i_terms_len {
        qz_i_terms.push(G1::deserialize_uncompressed(&mut file)?);
    }

    let qx_i_term = G1::deserialize_uncompressed(&mut file)?;
    let qx_i_term_mul_tau = G1::deserialize_uncompressed(&mut file)?;

    hints.push(Hint{
        i,
        pk_i,
        sk_i_l_i_of_tau_com_1,
        sk_i_l_i_of_tau_com_2,
        qz_i_terms,
        qx_i_term,
        qx_i_term_mul_tau,
    })


    }

   
    
    Ok(hints)
}
//multithreaded implementation 
#[allow(dead_code)]
fn hint_gen_test(n: usize, i: usize, sk_i: F, params: &UniversalParams<Curve>, pps: &PublicPolynomials) -> Hint {
    let l_i_of_x = &pps.l_i_of_x;
    //let z_of_x = &pps.z_of_x;
    let l_i_of_0_poly = &pps.l_i_of_zero_poly;

    let mut qz_terms = vec![];
    //let us compute the cross terms of q1
    for j in 0..n {

        let f = pps.cross_polynomials.get(j).unwrap();
        let sk_times_f = utils::poly_eval_mult_c(&f, &sk_i);

        let com = KZG::commit_g1(&params, &sk_times_f)
            .expect("commitment failed");

        qz_terms.push(com);
    }

     let x_monomial = utils::compute_x_monomial();
    // let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
    // let l_i_of_0_poly = utils::compute_constant_poly(&l_i_of_0);

    //numerator is l_i(x) - l_i(0)
    let num = l_i_of_x.sub(l_i_of_0_poly);
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
//multithreaded implementation 
#[allow(dead_code)]
fn generate_hint_and_write_test(
    params: &UniversalParams<Curve>,
    n: usize,  
    sk: Vec<F>,
    path: &str,
    pps : Vec<PublicPolynomials>
) -> Result<(), SerializationError> {
    let mut file = File::create(path).map_err(|e| SerializationError::IoError(e))?;
    let params = Arc::new(params) ;
   // let pps = Arc::new(pps);
    let hints = crossbeam::scope(|s| {
        let mut threads = Vec::new();
        for i in 0..n {
            //let idx = i.clone();
            //let n = n.clone();
            let sk = sk[i];
            let params = Arc::clone(&params) ;
            let pps = &pps[i];
           // println!("Spawning thread for index: {}", i) ;
            let thread_i = s.spawn(move |_| hint_gen_test(n,i,sk,&params,&pps));
            threads.push(thread_i);
        }

        threads.into_iter().map(|t| t.join().unwrap()).collect::<Vec<_>>()
    }).unwrap();

    (hints.len() as u64).serialize_uncompressed(&mut file)?;

    // Serialize each `Hint` in the vector
    for hint in hints {
        hint.i.serialize_uncompressed(&mut file)?;
        hint.pk_i.serialize_uncompressed(&mut file)?;
        hint.sk_i_l_i_of_tau_com_1.serialize_uncompressed(&mut file)?;
        hint.sk_i_l_i_of_tau_com_2.serialize_uncompressed(&mut file)?;

        // Serialize `qz_i_terms` vector length and elements
        (hint.qz_i_terms.len() as u64).serialize_uncompressed(&mut file)?;
        for term in &hint.qz_i_terms {
            term.serialize_uncompressed(&mut file)?;
        }

        hint.qx_i_term.serialize_uncompressed(&mut file)?;
        hint.qx_i_term_mul_tau.serialize_uncompressed(&mut file)?;
    }

    Ok(())
}

fn main() {

    //collecting command line arguments 
    let args: Vec<String> = env::args().collect() ;

    if args.len() != 4 {
        eprintln!(" Expected 3 arguments but got {}. \n\
        Usage: {} <n> <c> <t> \n\
        where:\n <n> is the universe size, <c> is the committee size, <t> is the threshold
        Example: {} 1024 64 23", 
        args.len() -1, 
        args.get(0).unwrap_or(&"program".to_string()),
        args.get(0).unwrap_or(&"program".to_string())
        ) ;
        std::process::exit(1) ;

    }
    //universe size is n 
    let n: usize = match args[1].parse() {
        Ok(num) if (num & (num -1) == 0) => num,
        _ => {
            eprintln!("the universe size must be a positive power of 2 ") ;
            std::process::exit(1) ;
        }
    } ;
    println!("n = {}", n);
    
    //committee size is c 
    let c: usize = match args[2].parse() {
        Ok(num) if (num > 0) => num,
        _ => {
            eprintln!("the committee size must be a positive number and a power of 2 ") ;
            std::process::exit(1) ;
        }
    } ;
    println!("c={}",c) ;

    //threshold is t
    let t: usize = match args[3].parse() {
        Ok(num) if (num > 0) => num,
        _ => {
            eprintln!("the threshold must be a positive number ") ;
            std::process::exit(1) ;
        }
    } ;
    println!("T={}",t) ;

    // -------------- sample one-time SRS ---------------
    //run KZG setup
    let rng = &mut test_rng();
    let start = Instant::now();
    let params: UniversalParams<ark_ec::bls12::Bls12<ark_bls12_381::Config>> = KZG::setup(n, rng).expect("Setup failed");
    let params = Arc::new(params) ;
    let duration = start.elapsed();
    println!("Time elapsed in KZG setup is: {:?}", duration);

    // -------------- sample universe specific values ---------------
    //sample random keys
    //let mut sk_file = File::open("../secret_keys256.bin").map_err(SerializationError::IoError);
    let secret_key_file = format!("secret_keys{}.bin",n);
    let sk = hintgen::read_secret_keys(&secret_key_file).unwrap() ;
   
   // read the hints and store it in a vector 
    let hints_file = format!("hints_test_data{}.bin",n) ;
    let all_parties_setup = read_hints_from_file(&hints_file).unwrap() ;

    //reading the hint independent elements that is the lagrange coefficients which is the most expensive computation
    //and storing them in a vector
    let setup_requirements = format!("setup_requirements{}.bin",n);
    let all_parties_independent_setup = read_hints_independent_compu_from_file(&setup_requirements).unwrap() ;
    //sample random weights for each party
    let weights = sample_weights(n - 1);

    //------------------------ONE TIME SETUP---------------------------------------
    let start = Instant::now();
    let (vk, ak) = setup(n, c,&params, &weights,  &all_parties_setup, &all_parties_independent_setup);
    let duration = start.elapsed();
    println!("Time elapsed in setup is: {:?}", duration);

   
    // -------------- sample proof specific values ---------------
    //have to use PRF to get c no of positions and also look for repititions
    let mut vrf = ECVRF::from_suite(CipherSuite::SECP256K1_SHA256_TAI).unwrap() ;
    let secret_key =
        hex::decode("c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721").unwrap();
    let public_key = vrf.derive_public_key(&secret_key).unwrap();
    let vrf_message: &[u8] = b"samplec" ;
    let pi = vrf.prove(&secret_key, &vrf_message).unwrap();

    let beta = vrf.verify(&public_key, &pi, &vrf_message);

   
    let bitmap_com = create_committee(c, n-1, &beta.unwrap()) ;
    let bitmap_signer = create_subset_bitmap(n - 1, &bitmap_com,t) ;



    let mut no_of_signers: usize = 0;

    for i in 0..bitmap_signer.len() {
        if bitmap_signer[i] == F::from(1) {
            no_of_signers = no_of_signers+1 ;
        }
    }

    println!("No. of signers is {}",no_of_signers) ;

    let message = "dyna-hinTs".as_bytes().to_vec();
    let dst = bls::DST_ETHEREUM.as_bytes().to_vec();

    //let sig_vec = partial_signatures_gen(n-1, &sk, &bitmap_signer, &message, &dst) ;
    let sig_vec = partial_signatures_gen_dleq(n-1, &sk, &bitmap_signer, &message, &dst, &ak.pks, &params);




    let start = Instant::now();
    let π = prove(&params, t,&ak, &vk, &bitmap_com, &bitmap_signer,&sig_vec, &message, &dst);
    let duration = start.elapsed();
    println!("Time elapsed in prover is: {:?}", duration);
    


       
    let start = Instant::now();
    verify(&vk, &π,t, &message, &dst,&mut vrf,&vrf_message, &pi, &public_key,&params);
    let duration = start.elapsed();
    println!("Time elapsed in verifier is: {:?}", duration);
       
    
    
   
   

   
}

fn setup(
    n: usize,
    c: usize,
    params: &UniversalParams<Curve>,
    w: &Vec<F>,
    all_parties_setup: &Vec<Hint>,
    all_parties_hint_independent_setup: &Vec<HintIndependentSetupElements>,
) -> (VerificationKey, AggregationKey)
{
    let mut weights = w.clone();
    weights.push(F::from(0));

    let w_of_x = utils::interpolate_poly_over_mult_subgroup(&weights);
    let w_of_x_com = KZG::commit_g1(&params, &w_of_x).unwrap();

    //allocate space to collect setup material from all n-1 parties
    let mut qz_contributions : Vec<Vec<G1>> = vec![Default::default(); n];
    let mut qx_contributions : Vec<G1> = vec![Default::default(); n];
    let mut qx_mul_tau_contributions : Vec<G1> = vec![Default::default(); n];
    let mut pks : Vec<G1> = vec![Default::default(); n];
    let mut sk_l_of_tau_coms: Vec<G2> = vec![Default::default(); n];
    
    //let start = Instant::now();

    //verify hint parallely

    crossbeam::scope(|s| {
        for i in 0..all_parties_setup.len() {
            let party = &all_parties_setup[i];
            let hint_ind = &all_parties_hint_independent_setup[i];
            s.spawn(move |_| {
                verify_hint(params, party, hint_ind);
            });
        }
    }).unwrap();
    //let duration = start.elapsed();
    //println!("time to verify hints is {:?}",duration);


    for hint in all_parties_setup {
        //extract necessary items for pre-processing
        qz_contributions[hint.i] = hint.qz_i_terms.clone();
        qx_contributions[hint.i] = hint.qx_i_term.clone();
        qx_mul_tau_contributions[hint.i] = hint.qx_i_term_mul_tau.clone();
        pks[hint.i] = hint.pk_i.clone();
        sk_l_of_tau_coms[hint.i] = hint.sk_i_l_i_of_tau_com_2.clone();
    }


    let z_of_x = utils::compute_vanishing_poly(n);
    let x_monomial = utils::compute_x_monomial();
    let l_n_minus_1_of_x = utils::lagrange_poly(n, n-1);

    let vp = VerificationKey {
        n: n,
        c: c,
        g_0: params.powers_of_g[0].clone(),
        h_0: params.powers_of_h[0].clone(),
        h_1: params.powers_of_h[1].clone(),
        l_n_minus_1_of_tau_com: KZG::commit_g1(&params, &l_n_minus_1_of_x).unwrap(),
        w_of_tau_com: w_of_x_com,
        sk_of_tau_com: add_all_g2(&params, &sk_l_of_tau_coms),
        z_of_tau_com: KZG::commit_g2(&params, &z_of_x).unwrap(),
        tau_com: KZG::commit_g2(&params, &x_monomial).unwrap(),
    };

    let pp = AggregationKey {
        n: n,
        c: c,
        weights: w.clone(),
        pks: pks,
        qz_terms: preprocess_qz_contributions(&qz_contributions),
        qx_terms: qx_contributions,
        qx_mul_tau_terms: qx_mul_tau_contributions,
    };

    (vp, pp)

}

//RO(SK, W, B, ParSum, Qx, Qz, Qx(τ ) · τ, Q) used to generate r 
fn random_oracle_r(
    sk_com: G2,
    w_com: G1,
    b_com: G1,
    parsum_com: G1,
    qx_com_signer: G1,
    qz_com_signer: G1,
    qx_mul_x_com_signer: G1,
    q_com: G1,
    q_sub_com: G1,
) -> F {

    let mut serialized_data = Vec::new();
    sk_com.serialize_compressed(&mut serialized_data).unwrap();
    w_com.serialize_compressed(&mut serialized_data).unwrap();
    b_com.serialize_compressed(&mut serialized_data).unwrap();
    parsum_com.serialize_compressed(&mut serialized_data).unwrap();
    qx_com_signer.serialize_compressed(&mut serialized_data).unwrap();
    qz_com_signer.serialize_compressed(&mut serialized_data).unwrap();
    qx_mul_x_com_signer.serialize_compressed(&mut serialized_data).unwrap();
    q_com.serialize_compressed(&mut serialized_data).unwrap();
    q_sub_com.serialize_compressed(&mut serialized_data).unwrap();
    
    


    let mut hash_result = Sha256::digest(serialized_data.as_slice());
    hash_result[31] = 0u8; //this makes sure we get a number below modulus
    let hash_bytes = hash_result.as_slice();

    let mut hash_values: [u64; 4] = [0; 4];
    hash_values[0] = u64::from_le_bytes(hash_bytes[0..8].try_into().unwrap());
    hash_values[1] = u64::from_le_bytes(hash_bytes[8..16].try_into().unwrap());
    hash_values[2] = u64::from_le_bytes(hash_bytes[16..24].try_into().unwrap());
    hash_values[3] = u64::from_le_bytes(hash_bytes[24..32].try_into().unwrap());
    //hash_values[3] = u64::from(0u64);

    let bi = BigInteger256::new(hash_values);

    //let input: [u8; 32] = [0u8; 32];
    F::try_from(bi).unwrap()
}

//random oracle to compute v to batch all the quotient polynomials in to one 
fn random_oracle_v(
    sk_com: G2,
    w_com: G1,
    b_com: G1,
    parsum_com: G1,
    qx_com_signer: G1,
    qz_com_signer: G1,
    qx_mul_x_com_signer: G1,
) -> F {

    let mut serialized_data = Vec::new();
    sk_com.serialize_compressed(&mut serialized_data).unwrap();
    w_com.serialize_compressed(&mut serialized_data).unwrap();
    b_com.serialize_compressed(&mut serialized_data).unwrap();
    parsum_com.serialize_compressed(&mut serialized_data).unwrap();
    qx_com_signer.serialize_compressed(&mut serialized_data).unwrap();
    qz_com_signer.serialize_compressed(&mut serialized_data).unwrap();
    qx_mul_x_com_signer.serialize_compressed(&mut serialized_data).unwrap();


    let mut hash_result = Sha256::digest(serialized_data.as_slice());
    hash_result[31] = 0u8; //this makes sure we get a number below modulus
    let hash_bytes = hash_result.as_slice();

    let mut hash_values: [u64; 4] = [0; 4];
    hash_values[0] = u64::from_le_bytes(hash_bytes[0..8].try_into().unwrap());
    hash_values[1] = u64::from_le_bytes(hash_bytes[8..16].try_into().unwrap());
    hash_values[2] = u64::from_le_bytes(hash_bytes[16..24].try_into().unwrap());
    hash_values[3] = u64::from_le_bytes(hash_bytes[24..32].try_into().unwrap());
    //hash_values[3] = u64::from(0u64);

    let bi = BigInteger256::new(hash_values);

    //let input: [u8; 32] = [0u8; 32];
    F::try_from(bi).unwrap()
}

fn prove(
    params: &UniversalParams<Curve>,
    t: usize,
    ak: &AggregationKey,
    vk: &VerificationKey,
    bitmap_com: &Vec<F>,
    bitmap_signer: &Vec<F>,
    signature_vector: &Vec<PartialSigDleq>,
    message: &Vec<u8>,
    dst: &Vec<u8>) -> Proof {

    let n = ak.n;

    //adjust the weights and bitmap polynomials
    let mut weights = ak.weights.clone();
    //compute sum of weights of active signers
    let total_active_weight = bitmap_signer
        .iter()
        .zip(weights.iter())
        .fold(F::from(0), |acc, (&x, &y)| acc + (x * y));
    //println!("total active weight is {:?}",total_active_weight) ;
    //weight's last element must the additive inverse of active weight
    weights.push(F::from(0) - total_active_weight);

    let mut bitmap_signer = bitmap_signer.clone();
    let mut bitmap_com = bitmap_com.clone() ;
   
   
    //compute B_com(x)-B_signer(x) to prove that B_signer is a subset of B_com
    let mut bitmap_sub = Vec::with_capacity(n) ;

    for (b1 ,b2) in bitmap_com.iter().zip(bitmap_signer.iter()) {
        if b1 != b2 {
            bitmap_sub.push(b1+b2) ;
        }
        else {
            bitmap_sub.push(F::from(0)) ;
        }
       
    }

    //weight vector for bitmap_sub 
    let mut sub_weights = ak.weights.clone() ;
    //sub_weight's last element must the additive inverse of weight_of_b_sub
    sub_weights.push(F::from(0) - F::from((ak.c-t ) as i128));

    //bitmap's last element must be 1
    bitmap_signer.push(F::from(1));
    bitmap_com.push(F::from(1));
    bitmap_sub.push(F::from(1)) ;

    //verify the partial signatures
    partial_signatures_verification_dleq(signature_vector, message, dst, &ak.pks, params);
    // partial_signatures_verification(signature_vector, message, dst, &ak.pks, params) ;
    let start = Instant::now() ;
    let agg_sigma = compute_agg_sig(signature_vector, n) ;
    let end = start.elapsed() ;
    println!("time to generate aggregated signature is {:?}",end) ;

    //compute all the scalars we will need in the prover
    let domain = Radix2EvaluationDomain::<F>::new(n as usize).unwrap();
    let ω: F = domain.group_gen;
    let ω_inv: F = F::from(1) / ω;

    //compute all the polynomials we will need in the prover
    let _z_of_x = utils::compute_vanishing_poly(n); //returns Z(X) = X^n - 1
    let l_n_minus_1_of_x = utils::lagrange_poly(n, n-1);
    let w_of_x = utils::interpolate_poly_over_mult_subgroup(&weights);
    let b_signer_of_x = utils::interpolate_poly_over_mult_subgroup(&bitmap_signer);
    //let b_committee_of_x = utils::interpolate_poly_over_mult_subgroup(&bitmap_com) ;
    let b_sub_of_x = utils::interpolate_poly_over_mult_subgroup(&bitmap_sub) ;
    let psw_of_x = compute_psw_poly(&weights, &bitmap_signer);
    let psw_of_x_div_ω = utils::poly_domain_mult_ω(&psw_of_x, &ω_inv);


    //more polynomials to prove B_signer is a subset of B_com 
    let w_sub_of_x = utils::interpolate_poly_over_mult_subgroup(&sub_weights) ;
    let psw_sub_of_x = compute_psw_poly(&sub_weights, &bitmap_sub) ;
    let psw_sub_of_x_div_ω = utils::poly_domain_mult_ω(&psw_sub_of_x, &ω_inv) ;
    //ParSumSubW_sub(x)=ParSumSubW_sub(X/ω) + W_sub(X).b_sub(X) + Z(X).Q1_sub(X)
    let t_of_x = psw_sub_of_x.sub(&psw_sub_of_x_div_ω).sub(&w_sub_of_x.mul(&b_sub_of_x));
    let psw_sub_wff_q_of_x = divide_by_vanishing_polynomial(&t_of_x, n);
    //L_{n−1}(X) · ParSumSubW(X) = Z(X) · Q2(X) 
    let t_of_x = l_n_minus_1_of_x.mul(&psw_sub_of_x);
    let psw_sub_check_q_of_x = divide_by_vanishing_polynomial(&t_of_x, n);
    //b_sub(X) · b_sub(X) − b_sub(X) = Z(X) · Q3(X)
    let t_of_x = b_sub_of_x.mul(&b_sub_of_x).sub(&b_sub_of_x);
    let b_sub_wff_q_of_x = divide_by_vanishing_polynomial(&t_of_x, n);
    //L_{n−1}(X) · (b_sub(X) - 1) = Z(X) · Q4(X)
    let t_of_x = l_n_minus_1_of_x.clone().mul(
        &b_sub_of_x.clone().sub(&utils::compute_constant_poly(&F::from(1))));
    let b_sub_check_q_of_x = divide_by_vanishing_polynomial(&t_of_x, n);



    //ParSumSignerW(X) = ParSumSignerW(X/ω) + W(X) · b_signer(X) + Z(X) · Q1(X)
    let t_of_x = psw_of_x.sub(&psw_of_x_div_ω).sub(&w_of_x.mul(&b_signer_of_x));
    let psw_wff_q_of_x = divide_by_vanishing_polynomial(&t_of_x, n);

    //L_{n−1}(X) · ParSumW(X) = Z(X) · Q2(X) 
    let t_of_x = l_n_minus_1_of_x.mul(&psw_of_x);
    let psw_check_q_of_x = divide_by_vanishing_polynomial(&t_of_x, n);

    //b_signer(X) · b_signer(X) − b_signer(X) = Z(X) · Q3(X)
    let t_of_x = b_signer_of_x.mul(&b_signer_of_x).sub(&b_signer_of_x);
    let b_wff_q_of_x = divide_by_vanishing_polynomial(&t_of_x, n);

    //L_{n−1}(X) · (b_signer(X) - 1) = Z(X) · Q4(X)
    let t_of_x = l_n_minus_1_of_x.clone().mul(
        &b_signer_of_x.clone().sub(&utils::compute_constant_poly(&F::from(1))));
    let b_check_q_of_x = divide_by_vanishing_polynomial(&t_of_x, n);

    let parsum_signer_of_tau_com = KZG::commit_g1(&params, &psw_of_x).unwrap();
    let b_signer_of_tau = KZG::commit_g1(&params, &b_signer_of_x).unwrap();
   // let b_committee_of_tau = KZG::commit_g1(&params, &b_committee_of_x).unwrap() ;
   let b_committee_of_tau = <<Curve as Pairing>::G1 as VariableBaseMSM>
    ::msm(&params.powers_of_g[0..n], &bitmap_com).unwrap().into_affine() ;
    let qz_com_signer = filter_and_add(&params, &ak.qz_terms, &bitmap_signer);
    let qx_com_signer = filter_and_add(&params, &ak.qx_terms, &bitmap_signer);
    let qx_mul_tau_com_signer = filter_and_add(&params, &ak.qx_mul_tau_terms, &bitmap_signer);

    let b_sub_of_tau = KZG::commit_g1(&params, &b_sub_of_x).unwrap() ;
    let parsum_sub_of_tau_com = KZG::commit_g1(&params, &psw_sub_of_x).unwrap();

//v using random oracle and computing v,v^2,v^3, v^4 
// to be used in computing q(x) = q1(x) + v q2(x) + v^2 q3(x) + v^3 q4(x)
let mut v1 = random_oracle_v(
    vk.sk_of_tau_com, 
    vk.w_of_tau_com,
    b_signer_of_tau,
    parsum_signer_of_tau_com,
    qx_com_signer,
    qz_com_signer,
    qx_mul_tau_com_signer,
);
let mut vec_v1 = vec![];
for _i in 0..4 {
    vec_v1.push(v1);
    v1 = v1 * v1 ;

}
  
   let mut q_of_x = psw_wff_q_of_x.clone()  ;
   for i in 0..(q_of_x.degree()+1) {
    q_of_x.coeffs[i] = q_of_x.coeffs[i] + vec_v1[0] * b_wff_q_of_x.coeffs[i] + vec_v1[1] * psw_check_q_of_x.coeffs[i]
                      + vec_v1[2]* b_check_q_of_x.coeffs[i]

   } ;
   let q_of_tau_com = KZG::commit_g1(&params, &q_of_x).unwrap() ;

   let mut q_sub_of_x = psw_sub_wff_q_of_x.clone()  ;
   for i in 0..(q_sub_of_x.degree()+1) {
    q_sub_of_x.coeffs[i] = q_sub_of_x.coeffs[i] + vec_v1[1] * b_sub_wff_q_of_x.coeffs[i] + vec_v1[2]* psw_sub_check_q_of_x.coeffs[i]
                      + vec_v1[3] * b_sub_check_q_of_x.coeffs[i]

   } ;
   let q_sub_of_tau_com = KZG::commit_g1(&params, &q_sub_of_x).unwrap() ;



    
    let agg_pk = compute_apk(&ak, &bitmap_signer);

   

    // RO(SK, W, B, ParSum, Qx, Qz, Qx(τ ) · τ, Q,Q_sub)
    let r = random_oracle_r(
        vk.sk_of_tau_com, 
        vk.w_of_tau_com,
        b_signer_of_tau,
        parsum_signer_of_tau_com,
        qx_com_signer,
        qz_com_signer,
        qx_mul_tau_com_signer,
        q_of_tau_com,
        q_sub_of_tau_com
    );
    let r_div_ω: F = r / ω;

    

    let psw_of_r_proof = KZG::compute_opening_proof(&params, &psw_of_x, &r).unwrap();
    let w_of_r_proof = KZG::compute_opening_proof(&params, &w_of_x, &r).unwrap();
    let b_signer_of_r_proof = KZG::compute_opening_proof(&params, &b_signer_of_x, &r).unwrap();
    let q_of_r_proof = KZG::compute_opening_proof(&params, &q_of_x, &r).unwrap();
    let q_sub_of_r_proof = KZG::compute_opening_proof(&params, &q_sub_of_x, &r).unwrap();


    //for sub vector 
    let psw_sub_of_r_proof = KZG::compute_opening_proof(&params, &psw_sub_of_x, &r).unwrap();
    let w_sub_of_r_proof = KZG::compute_opening_proof(&params, &w_sub_of_x, &r).unwrap();
    let b_sub_of_r_proof = KZG::compute_opening_proof(&params, &b_sub_of_x, &r).unwrap();

    //for r_div_ω
    let psw_sub_of_r_div_ω_proof = KZG::compute_opening_proof(&params, &psw_sub_of_x, &r_div_ω).unwrap();
    let psw_of_r_div_ω_proof = KZG::compute_opening_proof(&params, &psw_of_x, &r_div_ω).unwrap() ;

    let merged_proof: G1 = (psw_of_r_proof
        + w_of_r_proof.mul(r.pow([1]))
        + b_signer_of_r_proof.mul(r.pow([2]))
        + q_of_r_proof.mul(r.pow([3]))
        +psw_sub_of_r_proof.mul(r.pow([4]))
        + w_sub_of_r_proof.mul(r.pow([5]))
        + b_sub_of_r_proof.mul(r.pow([6]))
        + q_sub_of_r_proof.mul(r.pow([7]))).into();
    
    let merged_proof_at_r_div_ω : G1= (psw_sub_of_r_div_ω_proof
        + psw_of_r_div_ω_proof.mul(r_div_ω.pow([1]))).into() ;


    Proof {
        agg_pk: agg_pk.clone(),
        agg_sigma: agg_sigma.clone(),
        agg_weight: total_active_weight,
        
        parsum_signer_of_r_div_ω: psw_of_x.evaluate(&r_div_ω),
        parsum_sub_of_r_div_ω: psw_sub_of_x.evaluate(&r_div_ω),
        opening_proof_r_div_ω: merged_proof_at_r_div_ω,

        parsum_signer_of_r: psw_of_x.evaluate(&r),
        w_of_r: w_of_x.evaluate(&r),
        b_signer_of_r: b_signer_of_x.evaluate(&r),
        q_of_r: q_of_x.evaluate(&r),

        parsum_sub_of_r: psw_sub_of_x.evaluate(&r),
        w_sub_of_r: w_sub_of_x.evaluate(&r),
        q_sub_of_r: q_sub_of_x.evaluate(&r),
        b_sub_of_r: b_sub_of_x.evaluate(&r),

        
        opening_proof_r: merged_proof.into(),

        parsum_signer_of_tau_com: parsum_signer_of_tau_com,
        b_signer_of_tau: b_signer_of_tau,
        q_of_tau_com: q_of_tau_com,

        parsum_sub_of_tau_com: parsum_sub_of_tau_com,
        b_sub_of_tau: b_sub_of_tau,
        q_sub_of_tau_com: q_sub_of_tau_com,
        qz_of_tau_signer: qz_com_signer,
        qx_of_tau_signer: qx_com_signer,
        qx_of_tau_mul_tau_signer: qx_mul_tau_com_signer,

        b_committee_of_tau: b_committee_of_tau,
    }
}

//verify opening of the polynomial commitments
fn verify_openings_in_proof(vp: &VerificationKey, π: &Proof, r: F, t: usize) {
    //adjust the w_of_x_com
    let adjustment = F::from(0) - π.agg_weight;
    let adjustment_com = vp.l_n_minus_1_of_tau_com.mul(adjustment);
    let w_of_x_com: G1 = (vp.w_of_tau_com + adjustment_com).into();

    let adjustment_sub = F::from(0) - F::from((vp.c-t) as u64);
    let adjustment_sub_com = vp.l_n_minus_1_of_tau_com.mul(adjustment_sub);
    let w_sub_of_x_com: G1 = (vp.w_of_tau_com + adjustment_sub_com).into();

    let psw_sub_of_r_argument = π.parsum_sub_of_tau_com - vp.g_0.clone().mul(π.parsum_sub_of_r).into_affine();
    let w_sub_of_r_argument = w_sub_of_x_com - vp.g_0.clone().mul(π.w_sub_of_r).into_affine();
    let b_sub_of_r_argument = π.b_sub_of_tau - vp.g_0.clone().mul(π.b_sub_of_r).into_affine();
    let q_sub_of_r_argument =  π.q_sub_of_tau_com - vp.g_0.clone().mul(π.q_sub_of_r).into_affine();

    let psw_of_r_argument = π.parsum_signer_of_tau_com - vp.g_0.clone().mul(π.parsum_signer_of_r).into_affine();
    let w_of_r_argument = w_of_x_com - vp.g_0.clone().mul(π.w_of_r).into_affine();
    let b_signer_of_r_argument = π.b_signer_of_tau - vp.g_0.clone().mul(π.b_signer_of_r).into_affine();
    let q_of_r_argument =  π.q_of_tau_com - vp.g_0.clone().mul(π.q_of_r).into_affine();

    let merged_argument: G1 = (psw_of_r_argument
        + w_of_r_argument.mul(r.pow([1]))
        + b_signer_of_r_argument.mul(r.pow([2]))
        + q_of_r_argument.mul(r.pow([3]))
        +psw_sub_of_r_argument.mul(r.pow([4]))
        + w_sub_of_r_argument.mul(r.pow([5]))
        + b_sub_of_r_argument.mul(r.pow([6]))
        + q_sub_of_r_argument.mul(r.pow([7]))).into_affine();

    let lhs = <Curve as Pairing>::pairing(
        merged_argument, 
        vp.h_0);
    let rhs = <Curve as Pairing>::pairing(
        π.opening_proof_r, 
        vp.h_1 - vp.h_0.clone().mul(r).into_affine());
    assert_eq!(lhs, rhs);

    let domain = Radix2EvaluationDomain::<F>::new(vp.n as usize).unwrap();
    let ω: F = domain.group_gen;
    let r_div_ω: F = r / ω;

    let psw_sub_of_r_div_ω_argument = π.parsum_sub_of_tau_com - vp.g_0.clone().mul(π.parsum_sub_of_r_div_ω).into_affine();
    let psw_of_r_div_ω_argument = π.parsum_signer_of_tau_com - vp.g_0.clone().mul(π.parsum_signer_of_r_div_ω).into_affine();

    let merged_argument_at_r_div_ω : G1= (psw_sub_of_r_div_ω_argument
        + psw_of_r_div_ω_argument.mul(r_div_ω.pow([1]))).into() ;

        let lhs = <Curve as Pairing>::pairing(
            merged_argument_at_r_div_ω, 
            vp.h_0);
        let rhs = <Curve as Pairing>::pairing(
            π.opening_proof_r_div_ω, 
            vp.h_1 - vp.h_0.clone().mul(r_div_ω).into_affine());
        assert_eq!(lhs, rhs);

}

fn verify(vp: &VerificationKey, π: &Proof, t: usize, message: &Vec<u8>, dst: &Vec<u8>,vrf_instan: &mut ECVRF, vrf_message: &[u8], vrf_proof: &Vec<u8>, vrf_pk: &Vec<u8>,params: &UniversalParams<Curve>) {
     //let start = Instant::now();
    verify_committee(vp.c, vp.n-1, π.b_committee_of_tau,vrf_instan, vrf_message, vrf_proof, vrf_pk,params) ;
    //let duration = start.elapsed();
    //println!("time to verify committee is {:?}",duration);

    // compute root of unity
    let domain = Radix2EvaluationDomain::<F>::new(vp.n as usize).unwrap();
    let ω: F = domain.group_gen;

    //RO(SK, W, B, parsum_signer, Qx, Qz, Qx(τ ) · τ, Q1, Q2, Q3, Q4)
    let r = random_oracle_r(
        vp.sk_of_tau_com, 
        vp.w_of_tau_com,
        π.b_signer_of_tau,
        π.parsum_signer_of_tau_com,
        π.qx_of_tau_signer,
        π.qz_of_tau_signer,
        π.qx_of_tau_mul_tau_signer,
        π.q_of_tau_com,
        π.q_sub_of_tau_com,
    );

    let mut v1 = random_oracle_v(
        vp.sk_of_tau_com, 
        vp.w_of_tau_com,
        π.b_signer_of_tau,
        π.parsum_signer_of_tau_com,
        π.qx_of_tau_signer,
        π.qz_of_tau_signer,
        π.qx_of_tau_mul_tau_signer,
    );
    let mut vec_v1 = vec![];
    for _i in 0..4 {
        vec_v1.push(v1);
        v1 = v1 * v1 ;

    }


    // verify the polynomial openings at r and r / ω
    verify_openings_in_proof(vp, π, r,t);

    let n: u64 = vp.n as u64;
    // this takes logarithmic computation, but concretely efficient
    let vanishing_of_r: F = r.pow([n]) - F::from(1);

    // compute L_i(r) using the relation L_i(x) = Z_V(x) / ( Z_V'(x) (x - ω^i) )
    // where Z_V'(x)^-1 = x / N for N = |V|.
    let ω_pow_n_minus_1 = ω.pow([n-1]);
    let l_n_minus_1_of_r = (ω_pow_n_minus_1 / F::from(n)) * (vanishing_of_r / (r - ω_pow_n_minus_1));


    //assert polynomial identity B_sig(x) SK(x) = ask + Q_z(x) Z(x) + Q_x(x) x
    let lhs = <Curve as Pairing>::pairing(&π.b_signer_of_tau, &vp.sk_of_tau_com);
    let x1 = <Curve as Pairing>::pairing(&π.qz_of_tau_signer, &vp.z_of_tau_com);
    let x2 = <Curve as Pairing>::pairing(&π.qx_of_tau_signer, &vp.tau_com);
    let x3 = <Curve as Pairing>::pairing(&π.agg_pk, &vp.h_0);
    let rhs = x1.add(x2).add(x3);
    assert_eq!(lhs, rhs);


    //assert checks on the signer part proving threshold 
    let rhs = π.q_of_r * vanishing_of_r ;
    let lhs = (π.parsum_signer_of_r - π.parsum_signer_of_r_div_ω - π.w_of_r * π.b_signer_of_r)
                                                        + vec_v1[0] * (π.b_signer_of_r * π.b_signer_of_r - π.b_signer_of_r)
                                                        + vec_v1[1]*(l_n_minus_1_of_r * π.parsum_signer_of_r)
                                                        + vec_v1[2]*(l_n_minus_1_of_r * (π.b_signer_of_r - F::from(1))) ;
    assert_eq!(lhs,rhs) ;

    //..........................// for sub vector proving c-t weight 
    let rhs = π.q_sub_of_r * vanishing_of_r ;
    let lhs = (π.parsum_sub_of_r - π.parsum_sub_of_r_div_ω - π.w_sub_of_r * π.b_sub_of_r)
                                                        + vec_v1[1] * (π.b_sub_of_r * π.b_sub_of_r - π.b_sub_of_r)
                                                        + vec_v1[2]*(l_n_minus_1_of_r * π.parsum_sub_of_r)
                                                        + vec_v1[3]*(l_n_minus_1_of_r * (π.b_sub_of_r - F::from(1))) ;
    assert_eq!(lhs,rhs) ;

    //run the degree check e([Qx(τ)]_1, [τ]_2) ?= e([Qx(τ)·τ]_1, [1]_2)
    let lhs = <Curve as Pairing>::pairing(&π.qx_of_tau_signer, &vp.h_1);
    let rhs = <Curve as Pairing>::pairing(&π.qx_of_tau_mul_tau_signer, &vp.h_0);
    assert_eq!(lhs, rhs);
    bls::bls_verify(message, dst, π.agg_pk, &params, π.agg_sigma);

}


fn compute_apk(
    pp: &AggregationKey, 
    bitmap: &Vec<F>) -> G1 {
    let n = bitmap.len();
    let mut exponents: Vec<F> = vec![];
    let n_inv = F::from(1) / F::from(n as u64);
    for i in 0..n {
        let l_i_of_0 = n_inv;
        let active = bitmap[i] == F::from(1);
        exponents.push(if active { l_i_of_0 } else { F::from(0) });
    }

    <<Curve as Pairing>::G1 as VariableBaseMSM>
        ::msm(&pp.pks[..], &exponents).unwrap().into_affine()
}

fn compute_agg_sig(
    partial_sig_vec: &Vec<PartialSigDleq>,
    universe_size: usize,
) -> G2 {
    let mut exponents: Vec<F> = vec![];
    let mut temp = vec![] ;
    let n_inv = F::from(1) / F::from(universe_size as u64);
    for i in 0..partial_sig_vec.len() {
        exponents.push(n_inv) ;
        temp.push(partial_sig_vec[i].sigma) ;
    }
    


    <<Curve as Pairing>::G2 as VariableBaseMSM>
        ::msm(&temp[..], &exponents).unwrap().into_affine() 

}

fn preprocess_qz_contributions(
    q1_contributions: &Vec<Vec<G1>>
) -> Vec<G1> {
    let n = q1_contributions.len();
    let mut q1_coms = vec![];

    for i in 0..n {
        // extract party i's hints, from which we extract the term for i.
        let mut party_i_q1_com = q1_contributions[i][i].clone();
        for j in 0..n {
            if i != j {
                // extract party j's hints, from which we extract cross-term for party i
                let party_j_contribution = q1_contributions[j][i].clone();
                party_i_q1_com = party_i_q1_com.add(party_j_contribution).into();
            }
        }
        // the aggregation key contains a single term that 
        // is a product of all cross-terms and the ith term
        q1_coms.push(party_i_q1_com);
    }
    q1_coms
}

fn filter_and_add(
    params: &UniversalParams<Curve>, 
    elements: &Vec<G1>, 
    bitmap: &Vec<F>) -> G1 {
    let mut com = get_zero_poly_com_g1(&params);
    for i in 0..bitmap.len() {
        if bitmap[i] == F::from(1) {
            com = com.add(elements[i]).into_affine();
        }
    }
    com
}

fn add_all_g2(
    params: &UniversalParams<Curve>, 
    elements: &Vec<G2>) -> G2 {
    let mut com = get_zero_poly_com_g2(&params);
    for i in 0..elements.len() {
        com = com.add(elements[i]).into_affine();
    }
    com
}

fn get_zero_poly_com_g1(params: &UniversalParams<Curve>) -> G1 {
    let zero_poly = utils::compute_constant_poly(&F::from(0));
    KZG::commit_g1(&params, &zero_poly).unwrap()
}

fn get_zero_poly_com_g2(params: &UniversalParams<Curve>) -> G2 {
    let zero_poly = utils::compute_constant_poly(&F::from(0));
    KZG::commit_g2(&params, &zero_poly).unwrap()
}



fn compute_psw_poly(weights: &Vec<F>, bitmap: &Vec<F>) -> DensePolynomial<F> {
    let n = weights.len();
    let mut parsum = F::from(0);
    let mut evals = vec![];
    for i in 0..n {
        let w_i_b_i = bitmap[i] * weights[i];
        parsum += w_i_b_i;
        evals.push(parsum);
    }

    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let eval_form = Evaluations::from_vec_and_domain(evals, domain);
    eval_form.interpolate()
}

fn divide_by_vanishing_polynomial(
    polynomial: &DensePolynomial<F>,
    n: usize,
) -> DensePolynomial<F> {
    utils::divide_by_vanishing_polynomial(polynomial, n)
}

// some tests//
#[allow(dead_code)]
fn hint_independent_computation_test(n:usize,params: &UniversalParams<Curve>,i:usize, _z_of_x: &DensePolynomial<F>)-> HintIndependentSetupElements {

    
    let l_i_of_x = utils::lagrange_poly(n, i);
    //let z_of_x = &pps.z_of_x;
    

    let l_i_of_tau_com = KZG::commit_g2(&params, &l_i_of_x).expect("commitment failed");
    let mut cross_terms_com = vec![] ;
    let start = Instant::now();

    for j in 0..n {
        let num: DensePolynomial<F>;
        if i == j {
            
            num = l_i_of_x.clone().mul(&l_i_of_x).sub(&l_i_of_x);
           
        } else { //cross-terms
           
            let l_j_of_x = utils::lagrange_poly(n, j);
            num = l_j_of_x.mul(&l_i_of_x);
           
        }
        let f = divide_by_vanishing_polynomial(&num, n);
        cross_terms_com.push(KZG::commit_g2(&params, &f).expect("commitment failed"));
    }
    let duration = start.elapsed();
    println!("time to compute cross terms is {:?}",duration);
   
    let x_monomial = utils::compute_x_monomial();
    let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
    let l_i_of_0_poly = utils::compute_constant_poly(&l_i_of_0);
    let num = l_i_of_x.sub(&l_i_of_0_poly);
    //denominator is x
    let den = x_monomial.clone();

    //qx_term = (l_i(x) - l_i(0)) / x
    let qx_term = &num.div(&den);
    //qx_term_com = [ sk_i * (l_i(τ) - l_i(0)) / τ ]_1
    let qx_term_com = KZG::commit_g2(&params, &qx_term).expect("commitment failed");
    //qx_term_mul_tau = (l_i(x) - l_i(0))
    let qx_term_mul_tau = &num;
    //qx_term_mul_tau_com = [ (l_i(τ) - l_i(0)) ]_1
    let qx_term_mul_tau_com = KZG::commit_g2(&params, &qx_term_mul_tau).expect("commitment failed");
    HintIndependentSetupElements{
        i: i,
        l_i_of_tau_com_2: l_i_of_tau_com,
        qz_i_terms: cross_terms_com,
        qx_i_term: qx_term_com,
        qx_i_term_mul_tau: qx_term_mul_tau_com,
    }


}

#[allow(dead_code)]

// Function to process and serialize each chunk of computations
fn process_chunk(
    start: usize,
    end: usize,
    params: &Arc<UniversalParams<Curve>>,
    z_of_x: &Arc<DensePolynomial<F>>, 
    n: usize,

    file_path: &str,
) -> Result<(), SerializationError> {
    let file = File::create(file_path).map_err(|e| SerializationError::IoError(e))?;
    let mut writer = BufWriter::new(file);

    for i in start..end {
        let temp = hint_independent_computation_test(n, params, i, z_of_x);

        // Serialize each field of `temp`
        temp.i.serialize_uncompressed(&mut writer)?;
        temp.l_i_of_tau_com_2.serialize_uncompressed(&mut writer)?;
        temp.qx_i_term.serialize_uncompressed(&mut writer)?;
        temp.qx_i_term_mul_tau.serialize_uncompressed(&mut writer)?;

        // Serialize `qz_i_terms` vector length and elements
        ((temp.qz_i_terms).len() as u64).serialize_uncompressed(&mut writer)?;
        for term in &temp.qz_i_terms {
            term.serialize_uncompressed(&mut writer)?;
        }
    }

    writer.flush()?;
    Ok(())
}

// Main function using multithreading to generate hints and write results
#[allow(dead_code)]
fn generate_hints_independent_compu_and_write_test_1(
    params: UniversalParams<Curve>,
    n: usize,
    path: &str,
) -> Result<(), SerializationError> {
    let num_threads = 32;
    let chunk_size = (n + num_threads - 1) / num_threads; // Ensure all items are covered
    let params = Arc::new(params);
    let z_of_x = Arc::new(utils::compute_vanishing_poly(n));

    crossbeam::scope(|s| {
        for thread_id in 0..num_threads {
            let params = Arc::clone(&params);
            let z_of_x = Arc::clone(&z_of_x);

            // Determine start and end indices for each chunk
            let start = thread_id * chunk_size;
            let end = std::cmp::min(start + chunk_size, n);

            // Define unique file path for each thread
            let file_path = format!("{}_part_{}.bin", path, thread_id);

            s.spawn(move |_| {
                process_chunk(start, end, &params, &z_of_x,n, &file_path)
            });
        }
    }).unwrap();

    Ok(())
}

#[allow(dead_code)]
fn generate_setup_requirements_for_chunk(params: &Arc<UniversalParams<Curve>>, 
                               n: usize,
                               start: usize,
                               end: usize,
                               z_of_x: &Arc<DensePolynomial<F>>
                            )-> Vec<HintIndependentSetupElements> {
    
    let mut hint_inds_vec_1 = vec![];
    for i in start..end {
        let temp = hint_independent_computation_test(n, params, i, z_of_x);
        hint_inds_vec_1.push(temp);

    }
    hint_inds_vec_1
}

#[allow(dead_code)]
fn generate_setup_requirements(params: UniversalParams<Curve>,
                               n: usize
                            ) -> Vec<HintIndependentSetupElements>{


    let num_threads = 32;
    let chunk_size = (n + num_threads - 1) / num_threads; // Ensure all items are covered
    let params = Arc::new(params);
    let z_of_x = Arc::new(utils::compute_vanishing_poly(n));

    let mut complete_result = vec![];

    
                            
    crossbeam::scope(|s| {
        let mut hint_inds = vec![];
        for thread_id in 0..num_threads {
            let params = Arc::clone(&params);
            let z_of_x = Arc::clone(&z_of_x);
                            
             // Determine start and end indices for each chunk
            let start = thread_id * chunk_size;
            let end = std::cmp::min(start + chunk_size, n);
                            
                                        
            let hint_ind = s.spawn(move |_| {
               generate_setup_requirements_for_chunk(&params, n, start, end, &z_of_x)
            });
            hint_inds.push(hint_ind);
    }
    for temp in hint_inds{
        let result = temp.join().unwrap(); // Collect and unwrap each result
        complete_result.extend(result); // Merge each thread's vector into the final vector
    }
    }).unwrap();

    complete_result
                            
}



fn verify_hint(params: &UniversalParams<Curve>, hint: &Hint, hint_independents: &HintIndependentSetupElements) {
    let n = hint.qz_i_terms.len() ;
    //take n+3 no of random numbers to compute a random linear combination
    let mut random_numbers = Vec::with_capacity(n+3) ;
    let mut rng = ark_std::test_rng();
    let mut random_integer = F::rand(&mut rng) ;
    for _j in 0..n+3 {
        random_numbers.push(random_integer) ;
        random_integer = F::from(random_integer * random_integer) ;
        
    }
    let mut hints_linear_comb_left = vec![] ;
    hints_linear_comb_left.push(hint.sk_i_l_i_of_tau_com_1) ;
    hints_linear_comb_left.push(hint.qx_i_term) ;
    hints_linear_comb_left.push(hint.qx_i_term_mul_tau) ;
    for i in 0..n {
        hints_linear_comb_left.push(hint.qz_i_terms[i]) ;
    }

    let mut hints_linear_comb_right = vec![] ;
    hints_linear_comb_right.push(hint_independents.l_i_of_tau_com_2) ;
    hints_linear_comb_right.push(hint_independents.qx_i_term) ;
    hints_linear_comb_right.push(hint_independents.qx_i_term_mul_tau) ;
    for i in 0..n {
        hints_linear_comb_right.push(hint_independents.qz_i_terms[i]) ;
    }


   let lhs_pipenger = <<Curve as Pairing>::G1 as VariableBaseMSM>
    ::msm(&hints_linear_comb_left[..], &random_numbers).unwrap().into_affine() ;

    let rhs_pipenger =  <<Curve as Pairing>::G2 as VariableBaseMSM>
    ::msm(&hints_linear_comb_right[..], &random_numbers).unwrap().into_affine() ;

    let lhs =  <Curve as Pairing>::pairing(lhs_pipenger, params.powers_of_h[0]);
    let rhs = <Curve as Pairing>::pairing(hint.pk_i, rhs_pipenger);

    assert_eq!(lhs,rhs) ;

}

#[allow(dead_code)]

fn read_hints_independent_compu_from_file(path: &str) -> Result<Vec<HintIndependentSetupElements>, SerializationError> {
    let mut file = File::open(path).map_err(SerializationError::IoError)?;
            
        
    let hint_ind_count = u64::deserialize_uncompressed(&mut file)? as usize;
    let mut hints_independent_compu = Vec::with_capacity(hint_ind_count);
        
            // Deserialize each field from the file
    for _ in 0..hint_ind_count {
        let i = usize::deserialize_uncompressed(&mut file)?;
        let l_i_of_tau_com_2 = G2::deserialize_uncompressed(&mut file)?;
        let qx_i_term = G2::deserialize_uncompressed(&mut file)?;
        let qx_i_term_mul_tau = G2::deserialize_uncompressed(&mut file)?;
            // Deserialize the length of `qz_i_terms` and then each element
        let qz_i_terms_len = u64::deserialize_uncompressed(&mut file)? as usize;
        let mut qz_i_terms = Vec::with_capacity(qz_i_terms_len);
        for _ in 0..qz_i_terms_len {
            qz_i_terms.push(G2::deserialize_uncompressed(&mut file)?);
        }
        
        hints_independent_compu.push(HintIndependentSetupElements{
            i,
            l_i_of_tau_com_2,
            qz_i_terms,
            qx_i_term,
            qx_i_term_mul_tau,
        })
        
        
    }
        
           
            
    Ok(hints_independent_compu)
}


//-----------------------OPTIMIZED SETUP IMPLEMENTATION-----------------------------------//

#[allow(dead_code)]
//checking that e([L_i^2(t)/T(t)], [product L_j(t)]) = e([L_i(t)],[product L_i(t)L_j(t)/Z(t)])
fn checking_cross_terms_by_prover(params: &UniversalParams<Curve>,
                                  n: usize,
                                  i: usize,
                                  z_of_x: &DensePolynomial<F>, ) {
                                  //cross_terms: &Vec<Vec<G2>>) {
    let mut rng = ark_std::test_rng();

     let random_number = F::rand(&mut rng) ; 

     //this part is just to compare. in the protocol these cross terms will be generated by untrusted servers
     let start = Instant::now() ;
     let mut cross_terms  = vec![] ;
      
     for j in 0..n {
        let l_i_of_x = utils::lagrange_poly(n, i);
            if j != i {  
                let l_j_of_x = utils::lagrange_poly(n, j) ;
                let l_i_l_j_of_x = divide_by_vanishing_polynomial(&l_i_of_x.clone().mul(&l_j_of_x), n);
                let l_i_l_j_tau_com = KZG::commit_g1(&params, &l_i_l_j_of_x).expect("commitment failed") ;
                cross_terms.push(l_i_l_j_tau_com) ;
            }      
     }
     

     let duration = start.elapsed() ;
     println!("time to compute the cross terms are {:?}", duration) ;

     //this part is the optimized solution where aggregator will get the cross terms from
     //untrusted server and check their validity by using the pairing check 

    let z_of_tau_com = KZG::commit_g2(&params, &z_of_x).expect("commitment failed") ;
    //let inv_z_of_tau_com = -z_of_tau_com ;

    // this is the optimized part 
    let start = Instant::now() ;
     let mut scalars = vec![] ;
     // let mut cross_terms = vec![] ;
     let mut r_power = F::from(1) ;

     let mut left_linear_comb = vec![] ;

     let l_i_of_x = utils::lagrange_poly(n, i);
     let l_i_tau_com = KZG::commit_g2(&params, &l_i_of_x).expect("commitment failed") ;

     for j in 0..n {
        if j != i {
            let l_j_of_x = utils::lagrange_poly(n, j) ;
                //let l_i_l_j_of_x = l_i_of_x.clone().mul(&l_j_of_x) ;
            let l_j_tau_com = KZG::commit_g1(&params, &l_j_of_x).expect("commitment failed") ;
                //let l_i_l_j_tau_com = KZG::commit_g2(&params, &l_i_l_j_of_x).expect("commitment failed") ;
            left_linear_comb.push(l_j_tau_com) ;
                //cross_terms.push(l_i_l_j_tau_com) ;
            scalars.push(r_power) ;
                
            }
            r_power = r_power * random_number ;
        }

        let lhs_pip = <<Curve as Pairing>::G1 as VariableBaseMSM>::msm(
            &left_linear_comb,
            &scalars,
        )
        .unwrap()
        .into_affine();

        
        
        let rhs_pip = <<Curve as Pairing>::G1 as VariableBaseMSM>::msm(
            &cross_terms[..],
            &scalars,
        )
        .unwrap()
        .into_affine();
        
        //check e(g^{l_i(t)l_j(t)/Z(t)},g^{Z(t)})= e(g^{l_i(t)}, g^{l_j(t)}) and using random linear combination
        let lhs = <Curve as Pairing>::pairing( lhs_pip, l_i_tau_com);
        let rhs = <Curve as Pairing>::pairing(rhs_pip, z_of_tau_com);

        assert_eq!(lhs,rhs);
        let duration = start.elapsed() ;
        println!("time elapsed for the optimized check is {:?}", duration) ;
        
    }












        
    

#[cfg(test)]
mod tests {
    use ark_ec::short_weierstrass::Affine;

    use super::*;

    fn aggregate_sk(sk: &Vec<F>, bitmap: &Vec<F>) -> F {
        let n = sk.len();
        let mut agg_sk = F::from(0);
        for i in 0..sk.len() {
            let l_i_of_x = utils::lagrange_poly(n, i);
            let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
            agg_sk += bitmap[i] * sk[i] * l_i_of_0;
        }
        agg_sk
    }

    fn sanity_test_poly_domain_mult(
        f_of_x: &DensePolynomial<F>, 
        f_of_ωx: &DensePolynomial<F>, 
        ω: &F) {
        let mut rng = test_rng();
        let r = F::rand(&mut rng);
        let ωr: F = ω.clone() * r;
        assert_eq!(f_of_x.evaluate(&ωr), f_of_ωx.evaluate(&r));
    }

    fn sanity_test_b(
        b_signer_of_x: &DensePolynomial<F>,
        q_of_x: &DensePolynomial<F>
    ) {
    
        let mut rng = test_rng();
        let r = F::rand(&mut rng);
    
        let n: u64 = (b_signer_of_x.degree() + 1) as u64;
    
        let b_signer_of_r = b_signer_of_x.evaluate(&r);
        let q_of_r = q_of_x.evaluate(&r);
        let vanishing_of_r: F = r.pow([n]) - F::from(1);
    
        //ParSumW(ωr) − ParSumW(r) − W(ωr) · b(ωr) = Q2(r) · (r^n − 1)
        let left = b_signer_of_r * b_signer_of_r - b_signer_of_r;
        let right = q_of_r * vanishing_of_r;
        //println!("ParSumW(ωr) - ParSumW(r) - W(ωr)·b(ωr) = {:?}", tmp1);
        //println!("Q(r) · (r^n - 1) = {:?}", tmp2);
        assert_eq!(left, right);
    
    }
    
    fn sanity_test_psw(
        w_of_x: &DensePolynomial<F>,
        b_signer_of_x: &DensePolynomial<F>,
        psw_of_x: &DensePolynomial<F>,
        q_of_x: &DensePolynomial<F>
    ) {
    
        let mut rng = test_rng();
        let r = F::rand(&mut rng);
    
        let n: u64 = (b_signer_of_x.degree() + 1) as u64;
        let domain = Radix2EvaluationDomain::<F>::new(n as usize).unwrap();
        let ω: F = domain.group_gen;
        let ω_pow_n_minus_1: F = ω.pow([n-1]);
        let ωr: F = ω * r;
    
        let psw_of_r = psw_of_x.evaluate(&r);
        let psw_of_ωr = psw_of_x.evaluate(&ωr);
        let w_of_ωr = w_of_x.evaluate(&ωr);
        let b_of_ωr = b_signer_of_x.evaluate(&ωr);
        let q_of_r = q_of_x.evaluate(&r);
        let vanishing_of_r: F = r.pow([n]) - F::from(1);
    
        //ParSumW(ωr) − ParSumW(r) − W(ωr) · b(ωr) = Q2(r) · (r^n − 1)
        let tmp1 = psw_of_ωr - psw_of_r - w_of_ωr * b_of_ωr;
        let tmp2 = q_of_r * vanishing_of_r;
        //println!("ParSumW(ωr) - ParSumW(r) - W(ωr)·b(ωr) = {:?}", tmp1);
        //println!("Q(r) · (r^n - 1) = {:?}", tmp2);
        assert_eq!(tmp1, tmp2);
    
        //ParSumW(ωn−1) = 0
        let psw_of_ω_pow_n_minus_1 = psw_of_x.evaluate(&ω_pow_n_minus_1);
        //println!("ParSumW(ω^(n-1)) = {:?}", psw_of_ω_pow_n_minus_1);
        assert_eq!(psw_of_ω_pow_n_minus_1, F::from(0));
    
        //b(ωn−1) = 1
        let b_of_ω_pow_n_minus_1 = b_signer_of_x.evaluate(&ω_pow_n_minus_1);
        assert_eq!(b_of_ω_pow_n_minus_1, F::from(1));
    
    }

    #[test]
    fn sanity_test_public_part() {

        let weights: Vec<F> = vec![
            F::from(2), 
            F::from(3), 
            F::from(4), 
            F::from(5), 
            F::from(4), 
            F::from(3), 
            F::from(2), 
            F::from(0)-F::from(15)
        ];
        let bitmap: Vec<F> = vec![
            F::from(1),
            F::from(1), 
            F::from(0), 
            F::from(1), 
            F::from(0), 
            F::from(1), 
            F::from(1), 
            F::from(1)
        ];

        let n: u64 = bitmap.len() as u64;
        let domain = Radix2EvaluationDomain::<F>::new(n as usize).unwrap();
        let ω: F = domain.group_gen;

        let w_of_x = utils::interpolate_poly_over_mult_subgroup(&weights);
        let w_of_ωx = utils::poly_domain_mult_ω(&w_of_x, &ω);

        let b_signer_of_x = utils::interpolate_poly_over_mult_subgroup(&bitmap);
        let b_of_ωx = utils::poly_domain_mult_ω(&b_signer_of_x, &ω);

        let psw_of_x = compute_psw_poly(&weights, &bitmap);
        let psw_of_ωx = utils::poly_domain_mult_ω(&psw_of_x, &ω);

        //t(X) = ParSumW(ω · X) − ParSumW(X) − W(ω · X) · b(ω · X)
        let t_of_x = psw_of_ωx.sub(&psw_of_x).sub(&w_of_ωx.mul(&b_of_ωx));
        let z_of_x = utils::compute_vanishing_poly(n as usize); //returns Z(X) = X^n - 1
        let q2_of_x = divide_by_vanishing_polynomial(&t_of_x, n as usize);

        let t_of_x = b_signer_of_x.mul(&b_signer_of_x).sub(&b_signer_of_x);
        let q1_of_x = divide_by_vanishing_polynomial(&t_of_x, n as usize);
        
        sanity_test_poly_domain_mult(&w_of_x, &w_of_ωx, &ω);
        sanity_test_poly_domain_mult(&b_signer_of_x, &b_of_ωx, &ω);
        sanity_test_poly_domain_mult(&psw_of_x, &psw_of_ωx, &ω);

        sanity_test_psw(&w_of_x, &b_signer_of_x, &psw_of_x, &q2_of_x);
        sanity_test_b(&b_signer_of_x, &q1_of_x);
    }

    fn sanity_test_pssk(
        sk_of_x: &DensePolynomial<F>,
        b_signer_of_x: &DensePolynomial<F>,
        q1_of_x: &DensePolynomial<F>,
        q2_of_x: &DensePolynomial<F>,
        agg_sk: &F
    ) {
        let mut rng = test_rng();
        let r = F::rand(&mut rng);
        let n: u64 = (sk_of_x.degree() + 1) as u64;

        //SK(x) · B(x) − aSK = Q1(x) · Z(x) + Q2(x) · x
        let sk_of_r = sk_of_x.evaluate(&r);
        let b_signer_of_r = b_signer_of_x.evaluate(&r);
        let q1_of_r = q1_of_x.evaluate(&r);
        let z_of_r: F = r.pow([n]) - F::from(1);
        let q2_of_r = q2_of_x.evaluate(&r);

        let left = sk_of_r * b_signer_of_r;
        let right = (q1_of_r * z_of_r) + (q2_of_r * r) + agg_sk;
        assert_eq!(left, right);
    
    }
    #[test]
    fn bls_signature() {
        let n = 32 ;
        let rng = &mut test_rng();
        let params = KZG::setup(n, rng).expect("Setup failed");
    
    
        let sks: Vec<F> = hintgen::sample_secret_keys(n-1) ;
        let mut pks: Vec<G1> = vec![] ;
        for i in 0..n-1 {
            let sk_as_poly = utils::compute_constant_poly(&sks[i]) ;
            let pk = KZG::commit_g1(&params, &sk_as_poly).expect("commitment failed") ;
            pks.push(pk) ;
        }

    }

    #[test]
    fn sanity_test_secret_part() {
        //let weights: Vec<u64> = vec![2, 3, 4, 5, 4, 3, 2];
        let bitmap: Vec<F> = vec![
            F::from(1),
            F::from(1), 
            F::from(0), 
            F::from(1), 
            F::from(0), 
            F::from(1), 
            F::from(1), 
            F::from(1)
        ];

        let n = bitmap.len();

        let mut secret_keys: Vec<F> = hintgen::sample_secret_keys(n - 1);
        secret_keys.push(F::from(0));

        let agg_sk = aggregate_sk(&secret_keys, &bitmap);
        let sk_of_x = utils::interpolate_poly_over_mult_subgroup(&secret_keys);
        let b_signer_of_x = utils::interpolate_poly_over_mult_subgroup(&bitmap);
        let q1_of_x = compute_pssk_q1_poly(&secret_keys, &bitmap);
        let q2_of_x = compute_pssk_q2_poly(&secret_keys, &bitmap);

        sanity_test_pssk(&sk_of_x, &b_signer_of_x, &q1_of_x, &q2_of_x, &agg_sk);
    }

    fn compute_pssk_q1_poly(
        sk: &Vec<F>, 
        bitmap: &Vec<F>
    ) -> DensePolynomial<F> {
        let n = sk.len();
        //Li(x) · Li(x) − Li(x) / Z(x)
        let mut q1 = utils::compute_constant_poly(&F::from(0));

        for i in 0..n {
            if bitmap[i] == F::from(0) { continue; }

            let l_i_of_x = utils::lagrange_poly(n, i);
            let num = l_i_of_x.mul(&l_i_of_x).sub(&l_i_of_x);
            //let num = num.sub(&l_i_of_x);
            let f_i = divide_by_vanishing_polynomial(&num, n);
            let sk_i_f_i = utils::poly_eval_mult_c(&f_i, &sk[i]);

            q1 = q1.add(sk_i_f_i);

            let mut q1_inner = utils::compute_constant_poly(&F::from(0));
            for j in 0..n {
                if i == j { continue; } //i != j

                let l_j_of_x = utils::lagrange_poly(n, j);
                let num = l_j_of_x.mul(&l_i_of_x);
                let f_j = divide_by_vanishing_polynomial(&num, n);
                let sk_j_f_j = utils::poly_eval_mult_c(&f_j, &sk[j]);

                q1_inner = q1_inner.add(sk_j_f_j);
            }

            q1 = q1.add(q1_inner);
        }
        q1
    }

    fn compute_pssk_q2_poly(
        sk: &Vec<F>, 
        bitmap: &Vec<F>
    ) -> DensePolynomial<F> {
        let n = sk.len();
        let x_monomial = utils::compute_x_monomial();

        let mut q2 = utils::compute_constant_poly(&F::from(0));

        for i in 0..n {
            if bitmap[i] == F::from(0) { continue; }

            let l_i_of_x = utils::lagrange_poly(n, i);
            let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
            let l_i_of_0 = utils::compute_constant_poly(&l_i_of_0);
            let num = l_i_of_x.sub(&l_i_of_0);
            let den = x_monomial.clone();
            let f_i = num.div(&den);
            let sk_i_f_i = utils::poly_eval_mult_c(&f_i, &sk[i]);

            q2 = q2.add(sk_i_f_i);
        }
        q2
    }
    #[test]
    fn test_pipenger() {
        let n = 1024; 
        let mut rng = ark_std::test_rng();
        let params = KZG::setup(n, &mut rng).expect("Setup failed");
        let mut random_numbers = Vec::with_capacity(n+3) ;
        
    
       
        //let hint = hint_gen(&params,n,1,&sk) ;
        let mut hints_linear_comb_left = vec![] ;
        let g = params.powers_of_g[0];
        hints_linear_comb_left.push((g.mul(F::from(1))).into()) ;
        hints_linear_comb_left.push((g.mul(F::from(2))).into()) ;
        hints_linear_comb_left.push((g.mul(F::from(3))).into() );
        for _i in 0..n {
            hints_linear_comb_left.push(g) ;
        }

        let mut hints_linear_comb_right = vec![] ;
        let h = params.powers_of_h[0];
        hints_linear_comb_right.push((h.mul(F::from(1))).into()) ;
        hints_linear_comb_right.push((h.mul(F::from(2))).into()) ;
        hints_linear_comb_right.push((h.mul(F::from(3))).into() );
        for _i in 0..n {
            hints_linear_comb_right.push(h) ;
        }
    

        let mut random_integer = F::rand(&mut rng) ;
        for _j in 0..n+3 {
            random_numbers.push(random_integer) ;
            random_integer = F::from(random_integer * random_integer)  ;
        }
    let start = Instant::now() ;
     for _i in 0..10 {
        
            let _lhs_pipenger = <<Curve as Pairing>::G1 as VariableBaseMSM>
            ::msm(&hints_linear_comb_left[..], &random_numbers).unwrap().into_affine() ;
        
            let _rhs_pipenger =  <<Curve as Pairing>::G2 as VariableBaseMSM>
            ::msm(&hints_linear_comb_right[..], &random_numbers).unwrap().into_affine() ;
        }
     let duration = start.elapsed();
     println!("pippenger time is {:?}",duration) ;

       
    }
   #[test]
    fn generate_hints_and_sks_for_32() {
        let n = 32;
        let rng = &mut test_rng() ;
        let _=hintgen::write_secret_keys(n, "secret_keys32.bin");
        let sk = hintgen::read_secret_keys("secret_keys32.bin").unwrap();
        let params = KZG::setup(n,rng).unwrap() ;
        let start = Instant::now();
        let _=hintgen::generate_hints_and_write(&params, n, sk, "hints_test_data32.bin") ;
        let duration = start.elapsed();
        println!("time to generate hints is {:?}",duration);
        //let _=generate_hints_independent_compu_and_write(&params, n, "setup_requirements.bin") ;
    
    }
    // -----------------------These test functions generate hints, secret keys, lagrange coefficients for different universe sizes
    //and store them in particular files for the code to use them 
    #[test]
    fn generate_hints_independents_32_mult() {
        let n = 32;
        let rng = &mut test_rng() ;
        let params = KZG::setup(n,rng).unwrap() ;
        let mut _complete_setup_vec = vec![];
        let start = Instant::now() ;
        _complete_setup_vec = generate_setup_requirements(params, n) ;
        let duration = start.elapsed();

        println!("time to generate hints independent computations are {:?}",duration);

        let test_setup_vec = read_hints_independent_compu_from_file("setup_requirements32.bin").unwrap();
        assert_eq!(_complete_setup_vec, test_setup_vec);
       
        
    
    }

    #[test]
    fn generate_hints_and_sks_for_64() {
        let n = 64;
        let rng = &mut test_rng() ;
        let _=hintgen::write_secret_keys(n, "secret_keys64.bin");
        let sk = hintgen::read_secret_keys("secret_keys64.bin").unwrap();
        let params = KZG::setup(n,rng).unwrap() ;
         let start = Instant::now() ;

        let _=hintgen::generate_hints_and_write(&params, n, sk, "hints_test_data64.bin") ;
        let duration = start.elapsed();
        println!("time to generate hints is {:?}",duration) ;
    

    }
    #[test]
    fn generate_hints_independents_64_mult() {
        let n = 64;
        let rng = &mut test_rng() ;
        let params = KZG::setup(n,rng).unwrap() ;
        let mut _complete_setup_vec = vec![];
        let start = Instant::now() ;
        _complete_setup_vec = generate_setup_requirements(params, n) ;
        let duration = start.elapsed();

        println!("time to generate hints independent computations are {:?}",duration);

        let test_setup_vec = read_hints_independent_compu_from_file("setup_requirements64.bin").unwrap();
        assert_eq!(_complete_setup_vec, test_setup_vec);
       
        
    
    }
    #[test]
    fn generate_hints_and_sks_for_128() {
        let n = 128;
        let rng = &mut test_rng() ;
        let _=hintgen::write_secret_keys(n, "secret_keys128.bin");
        let sk = hintgen::read_secret_keys("secret_keys128.bin").unwrap();
        let params = KZG::setup(n,rng).unwrap() ;
        let start = Instant::now() ;
       let _= hintgen::generate_hints_and_write(&params, n, sk, "hints_test_data128.bin") ;
       let duration = start.elapsed();
        println!("time to generate hints is {:?}",duration) ;
    
    
    }
    #[test]
    fn generate_hints_independents_128_mult() {
        let n = 128;
        let rng = &mut test_rng() ;
        let params = KZG::setup(n,rng).unwrap() ;
        let mut _complete_setup_vec = vec![];
        let start = Instant::now() ;
        _complete_setup_vec = generate_setup_requirements(params, n) ;
        let duration = start.elapsed();

        println!("time to generate hints independent computations are {:?}",duration);

        let test_setup_vec = read_hints_independent_compu_from_file("setup_requirements128.bin").unwrap();
        assert_eq!(_complete_setup_vec, test_setup_vec);
       
        
    
    }

    
    #[test]
    fn generate_hints_and_sks_for_256() {
        let n = 256;
        let rng = &mut test_rng() ;
        let _=hintgen::write_secret_keys(n, "secret_keys256.bin");
        let sk = hintgen::read_secret_keys("secret_keys256.bin").unwrap();
        let params = KZG::setup(n,rng).unwrap() ;
        let start = Instant::now() ;
        let _=hintgen::generate_hints_and_write(&params, n, sk, "hints_test_data256.bin") ;
        let duration = start.elapsed();
        println!("time to generate hints is {:?}",duration) ;
    
    
    }
    #[test]
    fn generate_hints_independents_256_mult() {
        let n = 256;
        let rng = &mut test_rng() ;
        let params = KZG::setup(n,rng).unwrap() ;
        let mut _complete_setup_vec = vec![];
        let start = Instant::now() ;
        _complete_setup_vec = generate_setup_requirements(params, n) ;
        let duration = start.elapsed();

        println!("time to generate hints independent computations are {:?}",duration);

        let test_setup_vec = read_hints_independent_compu_from_file("setup_requirements256.bin").unwrap();
        assert_eq!(_complete_setup_vec, test_setup_vec);
       
        
    
    }
   
    #[test]
    fn generate_hints_and_sks_for_512() {
        let n = 512;
        let rng = &mut test_rng() ;
        let _=hintgen::write_secret_keys(n, "secret_keys512.bin");
        let sk = hintgen::read_secret_keys("secret_keys512.bin").unwrap();
        let params = KZG::setup(n,rng).unwrap() ;
        let start = Instant::now() ;
        let _=hintgen::generate_hints_and_write(&params, n, sk, "hints_test_data512.bin") ;
        let duration = start.elapsed();
        println!("time to generate hints is {:?}",duration) ;
    
    
    }
    #[test]
    fn generate_hints_independents_512_mult() {
        let n = 512;
        let rng = &mut test_rng() ;
        let params = KZG::setup(n,rng).unwrap() ;
        let mut _complete_setup_vec = vec![];
        //let pps = read_public_poly_from_file("public_poly_512.bin", n).expect("error in reading file");
        let start = Instant::now() ;
        _complete_setup_vec = generate_setup_requirements(params, n) ;
        //let _=generate_hints_independent_compu_and_write_test_1(params, n, "setup_requirements64_1") ;
        let duration = start.elapsed();

        println!("time to generate hints independent computations are {:?}",duration);

        let test_setup_vec = read_hints_independent_compu_from_file("setup_requirements512.bin").unwrap();
        assert_eq!(_complete_setup_vec, test_setup_vec);
       
        
    
    }
   
   
    #[test]
    fn generate_hints_and_sks_for_1024() {
        let n = 1024;
        let rng = &mut test_rng() ;
        let _= hintgen::write_secret_keys(n, "secret_keys1024.bin");
        let sk = hintgen::read_secret_keys("secret_keys1024.bin").unwrap();
        let params = KZG::setup(n,rng).unwrap() ;
        let start = Instant::now() ;
        let _=hintgen::generate_hints_and_write(&params, n, sk, "hints_test_data1024.bin") ;
        let duration = start.elapsed();
        println!("time to generate hints is {:?}",duration) ;
    
    }


    #[test]
    fn generate_hints_independents_1024_mult() {
        let n = 1024;
        let rng = &mut test_rng() ;
        let params = KZG::setup(n,rng).unwrap() ;
        let mut _complete_setup_vec = vec![];
        //let pps = read_public_poly_from_file("public_poly_512.bin", n).expect("error in reading file");
        let start = Instant::now() ;
        _complete_setup_vec = generate_setup_requirements(params, n) ;
        //let _=generate_hints_independent_compu_and_write_test_1(params, n, "setup_requirements64_1") ;
        let duration = start.elapsed();

        println!("time to generate hints independent computations are {:?}",duration);

        let test_setup_vec = read_hints_independent_compu_from_file("setup_requirements1024.bin").unwrap();
        assert_eq!(_complete_setup_vec, test_setup_vec);
       
        
    
    }


    #[test]
    fn generate_hints_and_sks_for_2048() {
        let n = 2048;
        let rng = &mut test_rng() ;
        let _= hintgen::write_secret_keys(n, "secret_keys2048.bin");
        let sk = hintgen::read_secret_keys("secret_keys2048.bin").unwrap();
        let params = KZG::setup(n,rng).unwrap() ;
        let start = Instant::now() ;
        let _=hintgen::generate_hints_and_write(&params, n, sk, "hints_test_data2048.bin") ;
        let duration = start.elapsed();
        println!("time to generate hints is {:?}",duration) ;
    
    
    }
    #[test]
    fn generate_hints_independents_2048_mult() {
        let n = 2048;
        let rng = &mut test_rng() ;
        let params = KZG::setup(n,rng).unwrap() ;
        //let pps = read_public_poly_from_file("public_poly_512.bin", n).expect("error in reading file");
        let start = Instant::now() ;
        let _=generate_hints_independent_compu_and_write_test_1(params, n, "setup_requirements2048_1") ;
        let duration = start.elapsed();
        println!("time to generate hints independent computations are {:?}",duration);
    
    }
    #[test]
    fn check_time_for_hints_independent_for_one_i_2048() {
        let n = 2048;
        let _= hintgen::write_secret_keys(n, "secret_keys2048.bin");
        let z_of_x = utils::compute_vanishing_poly(n) ;
        let sk = hintgen::read_secret_keys("secret_keys2048.bin").unwrap();
        let rng = &mut test_rng() ;
        let params = KZG::setup(n,rng).unwrap() ;
        let pps = generate_public_polynomials(n, 1, &z_of_x);
        let start = Instant::now();
        let hint = hint_gen_test(n, 1, sk[1], &params, &pps);
        let duration = start.elapsed();
        println!("time to generate hint is {:?}",duration);
        //let hint = hintgen::hint_gen(&params, n, 1, &sk[1]);
        let start = Instant::now() ;
        let hint_ind = hint_independent_computation_test(n, &params, 1, &z_of_x);
        let duration = start.elapsed() ;
        println!("Time to generate the hints independent polynomials for set up phase for i=1 is {:?}",duration);
        let start = Instant::now() ;
        verify_hint(&params, &hint, &hint_ind);
        let duration = start.elapsed();
        println!("time to verify hint using pippenger is {:?}",duration);

    }

    #[test]
    fn generate_hints_and_sks_for_4196() {
        let n = 4196;
        let rng = &mut test_rng() ;
        let _= hintgen::write_secret_keys(n, "secret_keys4196.bin");
        let sk = hintgen::read_secret_keys("secret_keys4196.bin").unwrap();
        let params = KZG::setup(n,rng).unwrap() ;
        let start = Instant::now() ;
        let _=hintgen::generate_hints_and_write(&params, n, sk, "hints_test_data4196.bin") ;
        let duration = start.elapsed();
        println!("time to generate hints is {:?}",duration) ;
    
    
    }
    #[test]
    fn generate_and_write_public_poly_for_4196() {
        let n=4196;
        //let rng = &mut test_rng() ;
        //let params = KZG::setup(n,rng).unwrap() ;
        //let params = Arc::new(params);
        let start= Instant::now();

        let _= generate_public_polys_and_write(n, "public_poly_4196.bin");
        let duration = start.elapsed();
        println!("Time to generate public poly in multi thread is {:?}",duration);
    }
    #[test]
    fn generate_hints_independents_4196_mult() {
        let n = 4196;
        let rng = &mut test_rng() ;
        let params = KZG::setup(n,rng).unwrap() ;
        //let pps = read_public_poly_from_file("public_poly_512.bin", n).expect("error in reading file");
        let start = Instant::now() ;
        let _=generate_hints_independent_compu_and_write_test_1(params, n, "setup_requirements4196_1") ;
        let duration = start.elapsed();
        println!("time to generate hints independent computations are {:?}",duration);
    
    }

    #[test]
    fn check_time_for_hints_independent_for_one_i_4096() {
        let n = 4096;
        let _= hintgen::write_secret_keys(n, "secret_keys4096.bin");
        let z_of_x = utils::compute_vanishing_poly(n) ;
        let sk = hintgen::read_secret_keys("secret_keys4096.bin").unwrap();
        let rng = &mut test_rng() ;
        let params = KZG::setup(n,rng).unwrap() ;
        let pps = generate_public_polynomials(n, 1, &z_of_x);
        let start = Instant::now();
        let hint = hint_gen_test(n, 1, sk[1], &params, &pps);
        let duration = start.elapsed();
        println!("time to generate hint is {:?}",duration);
        //let hint = hintgen::hint_gen(&params, n, 1, &sk[1]);
        let start = Instant::now() ;
        let hint_ind = hint_independent_computation_test(n, &params, 1, &z_of_x);
        let duration = start.elapsed() ;
        println!("Time to generate the hints independent polynomials for set up phase for i=1 is {:?}",duration);
        let start = Instant::now() ;
        verify_hint(&params, &hint, &hint_ind);
        let duration = start.elapsed();
        println!("time to verify hint using pippenger is {:?}",duration);

    }
    #[test]
    fn test_time_for_public_poly_2048() {
        let n = 2048;
        let i = 1;
        let z_of_x = utils::compute_vanishing_poly(n);
        let start = Instant::now();
        generate_public_polynomials(n, i, &z_of_x);
        let duration = start.elapsed();
        println!("time to generate one public poly for 2048 is {:?}",duration);
    }
    #[test]
    fn check_time_for_hints_independent_for_one_i_8192() {
        let n = 8192;
        let _= hintgen::write_secret_keys(n, "secret_keys8192.bin");
        let z_of_x = utils::compute_vanishing_poly(n) ;
        let sk = hintgen::read_secret_keys("secret_keys8192.bin").unwrap();
        let rng = &mut test_rng() ;
        let params = KZG::setup(n,rng).unwrap() ;
        let pps = generate_public_polynomials(n, 1, &z_of_x);
        let start = Instant::now();
        let hint = hint_gen_test(n, 1, sk[1], &params, &pps);
        let duration = start.elapsed();
        println!("time to generate hint is {:?}",duration);
        //let hint = hintgen::hint_gen(&params, n, 1, &sk[1]);
        let start = Instant::now() ;
        let hint_ind = hint_independent_computation_test(n, &params, 1, &z_of_x);
        let duration = start.elapsed() ;
        println!("Time to generate the hints independent polynomials for set up phase for i=1 is {:?}",duration);
        let start = Instant::now() ;
        verify_hint(&params, &hint, &hint_ind);
        let duration = start.elapsed();
        println!("time to verify hint using pippenger is {:?}",duration);

    }
    #[test]
    fn benchmarking_ak_vk() {
        let n = 8192;
        let rng = &mut test_rng();
        let params = KZG::setup(n,rng).unwrap() ;
        let mut weights = sample_weights(n - 1);
        weights.push(F::from(0));
        println!("length {}",weights.len());
        let mut rand_vec_g1 = vec![];
       let rand_grp1 = G1::rand(rng);
       for _i in 0..n {
        rand_vec_g1.push(rand_grp1);
       }
       let mut rand_vec_g2 = vec![];
       let rand_grp2 = G2::rand(rng);
       for _i in 0..n {
        rand_vec_g2.push(rand_grp2);
       }

       let mut vec_of_vec_g1 = vec![];
       for _i in 0..n {
        let temp = rand_vec_g1.clone();
        vec_of_vec_g1.push(temp);
       }
        let start = Instant::now();
        let w_of_x = utils::interpolate_poly_over_mult_subgroup(&weights);
        let _w_of_x_com = KZG::commit_g1(&params, &w_of_x).unwrap();
    
    
        let z_of_x = utils::compute_vanishing_poly(n);
        let x_monomial = utils::compute_x_monomial();
        let l_n_minus_1_of_x = utils::lagrange_poly(n, n-1);
        let _l_n_minus_1_of_tau_com =  KZG::commit_g1(&params, &l_n_minus_1_of_x).unwrap();
        let _z_of_tau_com = KZG::commit_g2(&params, &z_of_x).unwrap();
        let _tau_com = KZG::commit_g2(&params, &x_monomial).unwrap();
        let _sk_of_tau_com = add_all_g2(&params, &rand_vec_g2) ;
        let _qz_terms = preprocess_qz_contributions(&vec_of_vec_g1);
        let duration = start.elapsed();
        println!("for {} ak, vk is {:?}",n,duration);


    }

    #[test]
    fn benchmarking_ak_vk_2048() {
        let n = 2048;
        let rng = &mut test_rng();
        let params = KZG::setup(n,rng).unwrap() ;
        let mut weights = sample_weights(n - 1);
        weights.push(F::from(0));
        println!("length {}",weights.len());
        let mut rand_vec_g1 = vec![];
       let rand_grp1 = G1::rand(rng);
       for _i in 0..n {
        rand_vec_g1.push(rand_grp1);
       }
       let mut rand_vec_g2 = vec![];
       let rand_grp2 = G2::rand(rng);
       for _i in 0..n {
        rand_vec_g2.push(rand_grp2);
       }

       let mut vec_of_vec_g1 = vec![];
       for _i in 0..n {
        let temp = rand_vec_g1.clone();
        vec_of_vec_g1.push(temp);
       }
        let start = Instant::now();
        let w_of_x = utils::interpolate_poly_over_mult_subgroup(&weights);
        let _w_of_x_com = KZG::commit_g1(&params, &w_of_x).unwrap();
    
    
        let z_of_x = utils::compute_vanishing_poly(n);
        let x_monomial = utils::compute_x_monomial();
        let l_n_minus_1_of_x = utils::lagrange_poly(n, n-1);
        let _l_n_minus_1_of_tau_com =  KZG::commit_g1(&params, &l_n_minus_1_of_x).unwrap();
        let _z_of_tau_com = KZG::commit_g2(&params, &z_of_x).unwrap();
        let _tau_com = KZG::commit_g2(&params, &x_monomial).unwrap();
        let _sk_of_tau_com = add_all_g2(&params, &rand_vec_g2) ;
        let _qz_terms = preprocess_qz_contributions(&vec_of_vec_g1);
        let duration = start.elapsed();
        println!("for {} ak, vk is {:?}",n,duration);


    }

    #[test]
    fn benchmarking_ak_vk_4096() {
        let n = 4096;
        let rng = &mut test_rng();
        let params = KZG::setup(n,rng).unwrap() ;
        let mut weights = sample_weights(n - 1);
        weights.push(F::from(0));
        println!("length {}",weights.len());
        let mut rand_vec_g1 = vec![];
       let rand_grp1 = G1::rand(rng);
       for _i in 0..n {
        rand_vec_g1.push(rand_grp1);
       }
       let mut rand_vec_g2 = vec![];
       let rand_grp2 = G2::rand(rng);
       for _i in 0..n {
        rand_vec_g2.push(rand_grp2);
       }

       let mut vec_of_vec_g1 = vec![];
       for _i in 0..n {
        let temp = rand_vec_g1.clone();
        vec_of_vec_g1.push(temp);
       }
        let start = Instant::now();
        let w_of_x = utils::interpolate_poly_over_mult_subgroup(&weights);
        let _w_of_x_com = KZG::commit_g1(&params, &w_of_x).unwrap();
    
    
        let z_of_x = utils::compute_vanishing_poly(n);
        let x_monomial = utils::compute_x_monomial();
        let l_n_minus_1_of_x = utils::lagrange_poly(n, n-1);
        let _l_n_minus_1_of_tau_com =  KZG::commit_g1(&params, &l_n_minus_1_of_x).unwrap();
        let _z_of_tau_com = KZG::commit_g2(&params, &z_of_x).unwrap();
        let _tau_com = KZG::commit_g2(&params, &x_monomial).unwrap();
        let _sk_of_tau_com = add_all_g2(&params, &rand_vec_g2) ;
        let _qz_terms = preprocess_qz_contributions(&vec_of_vec_g1);
        let duration = start.elapsed();
        println!("for {} ak, vk is {:?}",n,duration);


    }

    #[test]
    fn testing_setup_optimization() {
        let n = 1024 ;
        let i = 2 ;
        let rng = &mut test_rng() ;
        let params = KZG::setup(n,rng).unwrap() ;
        let z_of_x = utils::compute_vanishing_poly(n);
        //let cross_terms = untrusted_server(&params, n, &z_of_x) ;
        checking_cross_terms_by_prover(&params, n, i, &z_of_x);
    }
}
