use anyhow::Result;
use ark_crypto_primitives::sponge::merlin::Transcript;
use ark_ff::UniformRand;
use ark_pallas::Fq;
use ark_pallas::Fr as Fp;
use ark_poly::DenseMVPolynomial;
use ark_poly::DenseMultilinearExtension;
use ark_poly::MultilinearExtension;
use ark_poly_commit::LabeledPolynomial;
use ark_poly_commit::PolynomialCommitment;

type PallasProjective = ark_pallas::Projective;
type PallasAffine = ark_pallas::Affine;
type PallasHyrax = ark_poly_commit::hyrax::HyraxPC<PallasAffine, DenseMultilinearExtension<Fp>>;

#[test]
fn hyrax_commit_and_open() -> Result<()> {
    // --- RNG ---
    let rng = &mut rand::thread_rng();

    // --- Parameters ---
    let max_degree = 4; // small for testing
    let num_vars = 8;
    println!("a");
    let pp = PallasHyrax::setup(max_degree, Some(num_vars), rng)?;

    println!("b");
    let (ck, vk) = PallasHyrax::trim(&pp, 0, 0, None)?;

    println!("c");
    let poly = ark_poly::DenseMultilinearExtension::rand(num_vars, rng);
    let labeled_poly = LabeledPolynomial::new("test".to_string(), poly, Some(max_degree), None);
    let labeled_polys = [labeled_poly.clone()];
    let (cms, states) = PallasHyrax::commit(&ck, &labeled_polys, Some(rng))?;
    let cm = cms[0].clone();

    println!("d");
    let points = vec![Fp::rand(rng); 8];
    let sponge = &mut Transcript::new(b"label");
    let pis = PallasHyrax::open(
        &ck,
        &labeled_polys,
        &cms,
        &points,
        sponge,
        &states,
        Some(rng),
    )?;
    let pi = pis[0].clone();

    println!("e");
    let value = labeled_poly.evaluate(&points);
    let sponge = &mut Transcript::new(b"label");
    let values = [value];
    let ok = PallasHyrax::check(&vk, &cms, &points, values, &pis, sponge, Some(rng))?;

    assert!(ok);
    Ok(())
}
