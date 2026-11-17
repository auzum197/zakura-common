//! The Orchard address signature circuit.
//!
//! This circuit enforces the Address signature statement: the spend authority and
//! diversified address integrity conditions of the Action statement, with `g_d` and
//! `pk_d` moved from the auxiliary input to the primary input.
//!
//! It uses a [narrow chip](chip) that has the constraint equations of the Action
//! circuit's gates in three advice columns, which makes the proof smaller.

use alloc::string::String;
#[cfg(feature = "prover")]
use alloc::vec::Vec;

use crate::backend::group::Curve;
#[cfg(feature = "prover")]
use crate::backend::halo2_proofs::transcript::Blake2bWrite;
use crate::backend::halo2_proofs::{
    circuit::{Layouter, Value, floor_planner},
    plonk,
    poly::commitment::Params,
};
#[cfg(feature = "verifier")]
use crate::backend::halo2_proofs::{plonk::SingleVerifier, transcript::Blake2bRead};
use crate::backend::pasta_curves::{arithmetic::CurveAffine, pallas, vesta};
#[cfg(feature = "prover")]
use rand::Rng;

use super::orchard_k11_params;
use crate::{
    constants::OrchardFixedBasesFull,
    keys::{
        CommitIvkRandomness, DiversifiedTransmissionKey, NullifierDerivingKey, SpendValidatingKey,
    },
    primitives::redpallas::{SpendAuth, VerificationKey},
    spec::NonIdentityPallasPoint,
};

mod chip;
#[cfg(test)]
mod reference;

/// Number of field elements in the primary input.
const INSTANCE_ROWS: usize = 6;

// Absolute offsets for public inputs. This is the primary input encoding of the
// Address signature statement.
const G_D_X: usize = 0;
const G_D_Y: usize = 1;
const PK_D_X: usize = 2;
const PK_D_Y: usize = 3;
const RK_X: usize = 4;
const RK_Y: usize = 5;

/// BLAKE2b personalization of a verifying key fingerprint. It is the personalization
/// of the Action circuit's fingerprint; the hashed descriptions differ.
const VK_FINGERPRINT_PERSONALIZATION: &[u8; 16] = b"Orchard-VkFprint";

/// Length in bytes of a verifying key fingerprint.
const VK_FINGERPRINT_LENGTH: usize = 32;

/// The address signature circuit.
#[derive(Clone)]
pub(crate) struct Circuit {
    g_d: Value<NonIdentityPallasPoint>,
    pk_d: Value<DiversifiedTransmissionKey>,
    ak: Value<SpendValidatingKey>,
    alpha: Value<pallas::Scalar>,
    nk: Value<NullifierDerivingKey>,
    rivk: Value<CommitIvkRandomness>,
}

impl core::fmt::Debug for Circuit {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("address_signature::Circuit([redacted])")
    }
}

impl Circuit {
    /// A circuit without witnesses, for key generation.
    pub(crate) fn empty() -> Self {
        Circuit {
            g_d: Value::unknown(),
            pk_d: Value::unknown(),
            ak: Value::unknown(),
            alpha: Value::unknown(),
            nk: Value::unknown(),
            rivk: Value::unknown(),
        }
    }

    /// Constructs the circuit from the auxiliary input, and the two address points of
    /// the primary input.
    #[cfg(feature = "prover")]
    pub(crate) fn new(
        address: &crate::Address,
        ak: SpendValidatingKey,
        alpha: crate::primitives::redpallas::SpendAuthRandomizer,
        nk: NullifierDerivingKey,
        rivk: CommitIvkRandomness,
    ) -> Self {
        Circuit {
            g_d: Value::known(address.g_d()),
            pk_d: Value::known(*address.pk_d()),
            ak: Value::known(ak),
            alpha: Value::known(alpha.scalar()),
            nk: Value::known(nk),
            rivk: Value::known(rivk),
        }
    }
}

impl plonk::Circuit<pallas::Base> for Circuit {
    type Config = chip::Config;
    type FloorPlanner = floor_planner::V1;

    fn without_witnesses(&self) -> Self {
        Self::empty()
    }

    fn configure(meta: &mut plonk::ConstraintSystem<pallas::Base>) -> Self::Config {
        chip::Config::configure(meta)
    }

    #[allow(non_snake_case)]
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<pallas::Base>,
    ) -> Result<(), plonk::Error> {
        // Load the Sinsemilla generator lookup table used by the whole self.
        config.load_table(&mut layouter)?;

        // Witness g_d and bind it to the primary input.
        let g_d = config.witness_point(
            layouter.namespace(|| "witness g_d"),
            self.g_d.as_ref().map(|g_d| g_d.to_affine()),
        )?;
        config.constrain_instance(&mut layouter, &g_d.x, G_D_X)?;
        config.constrain_instance(&mut layouter, &g_d.y, G_D_Y)?;

        // Witness ak_P.
        let ak_P = config.witness_point(
            layouter.namespace(|| "witness ak_P"),
            self.ak.as_ref().map(|ak| ak.to_point().to_affine()),
        )?;

        // Spend authority (https://p.z.cash/ZKS:action-spend-authority)
        {
            // alpha_commitment = [alpha] SpendAuthG
            let alpha_commitment = config.mul_fixed(
                layouter.namespace(|| "[alpha] SpendAuthG"),
                &OrchardFixedBasesFull::SpendAuthG,
                self.alpha,
            )?;

            // [alpha] SpendAuthG + ak_P
            let rk = config.add(layouter.namespace(|| "rk"), &alpha_commitment, &ak_P)?;

            // Constrain rk to equal public input
            config.constrain_instance(&mut layouter, &rk.x, RK_X)?;
            config.constrain_instance(&mut layouter, &rk.y, RK_Y)?;
        }

        // Diversified address integrity (https://p.z.cash/ZKS:action-addr-integrity?partial).
        {
            // ak = Extract_P(ak_P) is the x-coordinate of the non-identity point.
            let ivk = config.commit_ivk(
                layouter.namespace(|| "CommitIvk"),
                &ak_P.x,
                self.nk.map(|nk| nk.inner()),
                self.rivk.map(|rivk| rivk.inner()),
            )?;

            // [ivk] g_d
            let derived_pk_d = config.mul(layouter.namespace(|| "[ivk] g_d"), &ivk, &g_d)?;

            // Constrain the derived point to be a non-identity point, and bind it to
            // the primary input.
            let pk_d = config.check_point(layouter.namespace(|| "pk_d"), &derived_pk_d)?;
            config.constrain_instance(&mut layouter, &pk_d.x, PK_D_X)?;
            config.constrain_instance(&mut layouter, &pk_d.y, PK_D_Y)?;
        }

        Ok(())
    }
}

/// The primary input of the Address signature statement.
///
/// # Invariants
///
/// `rk` is not the identity. The address points are non-identity by construction.
#[derive(Clone, Debug)]
pub(crate) struct Instance {
    g_d: NonIdentityPallasPoint,
    pk_d: DiversifiedTransmissionKey,
    rk: VerificationKey<SpendAuth>,
}

impl Instance {
    /// Returns `None` if `rk` is the identity.
    pub(crate) fn new(address: &crate::Address, rk: &VerificationKey<SpendAuth>) -> Option<Self> {
        (!rk.is_identity()).then(|| Instance {
            g_d: address.g_d(),
            pk_d: *address.pk_d(),
            rk: rk.clone(),
        })
    }

    fn to_halo2_instance(&self) -> [vesta::Scalar; INSTANCE_ROWS] {
        let points = [*self.g_d, *self.pk_d.inner(), self.rk.point()];
        let mut affine = [pallas::Affine::default(); 3];
        pallas::Point::batch_normalize(&points, &mut affine);
        let [g_d, pk_d, rk] = affine.map(|point| {
            point
                .coordinates()
                .expect("every instance point is non-identity by construction")
        });

        let mut instance = [vesta::Scalar::zero(); INSTANCE_ROWS];
        instance[G_D_X] = *g_d.x();
        instance[G_D_Y] = *g_d.y();
        instance[PK_D_X] = *pk_d.x();
        instance[PK_D_Y] = *pk_d.y();
        instance[RK_X] = *rk.x();
        instance[RK_Y] = *rk.y();
        instance
    }
}

/// The verifying key for the Orchard address signature circuit, version 1.
#[derive(Debug)]
pub struct VerifyingKey {
    params: Params<vesta::Affine>,
    vk: plonk::VerifyingKey<vesta::Affine>,
}

impl VerifyingKey {
    /// Builds the verifying key.
    pub fn build() -> Self {
        let params = orchard_k11_params();
        let vk = plonk::keygen_vk(&params, &Circuit::empty())
            .expect("the address signature circuit is well formed");
        VerifyingKey { params, vk }
    }

    /// The pinned circuit description of this verifying key.
    pub(crate) fn pinned_description(&self) -> String {
        format!("{:#?}\n", self.vk.pinned())
    }

    /// A 32-byte fingerprint of this verifying key: BLAKE2b-256 over the pinned key
    /// description, personalized with `Orchard-VkFprint`.
    ///
    /// A verifier can pin this value, so that a circuit change is a deliberate version
    /// change and not a silent dependency update.
    pub fn fingerprint(&self) -> [u8; VK_FINGERPRINT_LENGTH] {
        let hash = blake2b_simd::Params::new()
            .hash_length(VK_FINGERPRINT_LENGTH)
            .personal(VK_FINGERPRINT_PERSONALIZATION)
            .hash(self.pinned_description().as_bytes());
        let mut out = [0u8; VK_FINGERPRINT_LENGTH];
        out.copy_from_slice(hash.as_bytes());
        out
    }
}

/// The proving key for the Orchard address signature circuit, version 1.
#[derive(Debug)]
pub struct ProvingKey {
    params: Params<vesta::Affine>,
    pk: plonk::ProvingKey<vesta::Affine>,
}

impl ProvingKey {
    /// Builds the proving key.
    pub fn build() -> Self {
        let params = orchard_k11_params();
        let circuit = Circuit::empty();
        let vk = plonk::keygen_vk(&params, &circuit)
            .expect("the address signature circuit is well formed");
        let pk = plonk::keygen_pk(&params, vk, &circuit)
            .expect("the address signature circuit is well formed");
        ProvingKey { params, pk }
    }

    /// Returns the [`VerifyingKey`] that corresponds to this proving key.
    ///
    /// This clones the key material in the proving key. It does not do key generation.
    pub fn verifying_key(&self) -> VerifyingKey {
        VerifyingKey {
            params: self.params.clone(),
            vk: self.pk.get_vk().clone(),
        }
    }
}

/// Creates a proof of the Address signature statement.
#[cfg(feature = "prover")]
pub(crate) fn create_proof(
    pk: &ProvingKey,
    circuit: Circuit,
    instance: &Instance,
    rng: &mut dyn Rng,
) -> Result<Vec<u8>, plonk::Error> {
    let instance = instance.to_halo2_instance();
    let mut transcript = Blake2bWrite::<_, vesta::Affine, _>::init(vec![]);
    plonk::create_proof(
        &pk.params,
        &pk.pk,
        &[circuit],
        &[&[&instance[..]]],
        rng,
        &mut transcript,
    )?;
    Ok(transcript.finalize())
}

/// Verifies a proof of the Address signature statement.
///
/// This ignores bytes that follow the proof. The caller must check the proof length.
#[cfg(feature = "verifier")]
pub(crate) fn verify_proof(
    vk: &VerifyingKey,
    instance: &Instance,
    proof: &[u8],
) -> Result<(), plonk::Error> {
    let instance = instance.to_halo2_instance();
    let strategy = SingleVerifier::new(&vk.params);
    let mut transcript = Blake2bRead::init(proof);
    plonk::verify_proof(
        &vk.params,
        &vk.vk,
        strategy,
        &[&[&instance[..]]],
        &mut transcript,
    )
}

#[cfg(all(test, feature = "prover", feature = "verifier"))]
mod tests {
    use alloc::vec::Vec;

    use crate::backend::halo2_proofs::{
        dev::{CircuitCost, MockProver},
        plonk,
    };
    use crate::backend::pasta_curves::{pallas, vesta};
    use proptest::prelude::*;

    use super::{
        Circuit, Instance, VerifyingKey,
        chip::fault::{self, Position},
        reference::ReferenceCircuit,
    };
    use crate::{
        Address,
        address::testing::arb_address,
        address_signature::spend_authority::PROOF_SIZE,
        circuit::halo2::K,
        keys::{
            Diversifier, FullViewingKey, Scope, SpendAuthorizingKey, SpendValidatingKey,
            SpendingKey, testing::arb_spending_key,
        },
        primitives::redpallas::{SpendAuthRandomizer, testing::arb_spend_auth_randomizer},
    };

    /// Number of proptest cases. Each case runs the mock prover many times.
    const CASES: u32 = 3;

    /// Number of witnessed cells that one case of the sampled fault test changes.
    const SAMPLED_FAULTS: usize = 24;

    /// Path of the pinned version 1 circuit description, from the crate root.
    const PINNED_DESCRIPTION_PATH: &str =
        "src/circuit_data/circuit_description_address_signature_v1";

    /// The pinned fingerprint of the version 1 verifying key.
    const PINNED_FINGERPRINT: &str =
        include_str!("../../circuit_data/circuit_fingerprint_address_signature_v1");

    /// Path of the pinned version 1 fingerprint, from the crate root.
    const PINNED_FINGERPRINT_PATH: &str =
        "src/circuit_data/circuit_fingerprint_address_signature_v1";

    /// Environment variable that regenerates the pinned files instead of checking them.
    const REGENERATE_ENV: &str = "ORCHARD_CIRCUIT_TEST_GENERATE_NEW_PROOF";

    /// Witnessed cells that the constraints do not determine for each witness. The
    /// complete addition gate of the Action circuit leaves the same cells free.
    ///
    /// - `alpha = inv0(x_q - x_p)` of a complete addition is free when `x_q = x_p`.
    ///   The gate multiplies it by `x_q - x_p`. This occurs in the doubling of the
    ///   base in variable-base scalar multiplication.
    /// - `beta = inv0(x_p)` of a complete addition is free when `P` is the identity.
    ///   The gate multiplies it by `x_p`. This occurs in the addition for the least
    ///   significant bit, when that bit is 1.
    /// - `eta = inv0(z_130)` of the overflow check is free when `k_254 = 1`.
    const FREE_AUXILIARY_CELLS: [Position; 3] = [
        ("complete addition", 2, 1),
        ("complete addition", 2, 2),
        ("variable-base mul (overflow check)", 0, 2),
    ];

    fn arb_scope() -> impl Strategy<Value = Scope> {
        prop_oneof![Just(Scope::External), Just(Scope::Internal)]
    }

    prop_compose! {
        /// Generates a spending key, one of its addresses, and the scope of the address.
        fn arb_key_and_address()(
            sk in arb_spending_key(),
            d in prop::array::uniform11(any::<u8>()),
            scope in arb_scope(),
        ) -> (SpendingKey, Address, Scope) {
            let address = FullViewingKey::from(&sk).address(Diversifier::from_bytes(d), scope);
            (sk, address, scope)
        }
    }

    fn other_scope(scope: Scope) -> Scope {
        match scope {
            Scope::External => Scope::Internal,
            Scope::Internal => Scope::External,
        }
    }

    fn spend_validating_key(sk: &SpendingKey) -> SpendValidatingKey {
        SpendValidatingKey::from(&SpendAuthorizingKey::from(sk))
    }

    fn circuit_and_instance(
        sk: &SpendingKey,
        address: &Address,
        scope: Scope,
        alpha: SpendAuthRandomizer,
    ) -> (Circuit, Instance) {
        let fvk = FullViewingKey::from(sk);
        let ak = spend_validating_key(sk);
        let rk = ak.randomize(&alpha);
        let circuit = Circuit::new(address, ak, alpha, *fvk.nk(), fvk.rivk(scope));
        let instance = Instance::new(address, &rk).expect("rk is not the identity");
        (circuit, instance)
    }

    fn mock_verify(circuit: &impl plonk::Circuit<pallas::Base>, instance: &Instance) -> bool {
        MockProver::run(K, circuit, vec![instance.to_halo2_instance().to_vec()])
            .unwrap()
            .verify()
            .is_ok()
    }

    /// Whether the circuit accepts. The reference circuit must agree.
    fn accepts(circuit: &Circuit, instance: &Instance) -> bool {
        let accepted = mock_verify(circuit, instance);
        assert_eq!(
            accepted,
            mock_verify(&ReferenceCircuit(circuit.clone()), instance),
            "the narrow chip and the reference chips disagree"
        );
        accepted
    }

    /// Changes the witnessed cell `index`, and returns whether the circuit accepts.
    fn accepts_fault(circuit: &Circuit, instance: &Instance, index: usize) -> bool {
        fault::set_target(Some(index));
        let accepted = mock_verify(circuit, instance);
        fault::set_target(None);
        accepted
    }

    /// The witnessed cells of one synthesis.
    fn witnessed_cells(circuit: &Circuit, instance: &Instance) -> Vec<Position> {
        fault::set_target(None);
        assert!(mock_verify(circuit, instance));
        fault::assigned()
    }

    #[test]
    fn proof_size_matches_constant() {
        let cost = CircuitCost::<vesta::Point, _>::measure(K, &Circuit::empty());
        assert_eq!(usize::from(cost.proof_size(1)), PROOF_SIZE);

        // The narrow chip must give a smaller proof than the Action circuit's chips.
        let reference =
            CircuitCost::<vesta::Point, _>::measure(K, &ReferenceCircuit(Circuit::empty()));
        assert!(PROOF_SIZE < usize::from(reference.proof_size(1)));
    }

    #[test]
    fn circuit_description_is_pinned() {
        let vk = VerifyingKey::build();
        let fingerprint = hex::encode(vk.fingerprint());

        if std::env::var_os(REGENERATE_ENV).is_some() {
            std::fs::write(PINNED_DESCRIPTION_PATH, vk.pinned_description())
                .expect("should be able to write the circuit description");
            std::fs::write(PINNED_FINGERPRINT_PATH, format!("{fingerprint}\n"))
                .expect("should be able to write the fingerprint");
        } else {
            assert_eq!(
                vk.pinned_description(),
                include_str!("../../circuit_data/circuit_description_address_signature_v1")
                    .replace("\r\n", "\n")
            );
            assert_eq!(fingerprint, PINNED_FINGERPRINT.trim());
        }
    }

    /// Changes every witnessed cell in turn. The circuit must reject each change,
    /// except a change of a cell in [`FREE_AUXILIARY_CELLS`].
    ///
    /// This takes minutes. `sampled_faults_are_rejected` runs a sample by default.
    #[test]
    #[ignore]
    fn all_faults_are_rejected() {
        let sk = SpendingKey::from_bytes([7; 32]).unwrap();
        let address =
            FullViewingKey::from(&sk).address(Diversifier::from_bytes([3; 11]), Scope::External);
        let alpha = SpendAuthRandomizer::from_bytes([1; 32]).unwrap();
        let (circuit, instance) = circuit_and_instance(&sk, &address, Scope::External, alpha);

        let cells = witnessed_cells(&circuit, &instance);
        let accepted: Vec<_> = cells
            .iter()
            .enumerate()
            .filter(|(index, _)| accepts_fault(&circuit, &instance, *index))
            .map(|(_, cell)| *cell)
            .collect();
        assert!(
            accepted
                .iter()
                .all(|cell| FREE_AUXILIARY_CELLS.contains(cell)),
            "the circuit accepts a change of {accepted:?}"
        );
    }

    /// A prover uses its own base in the incomplete chain of `[ivk] g_d`, with all
    /// other cells consistent, and claims the point that this gives as `pk_d`. This
    /// is the attack of CVE-2026-54496. Every gate is satisfied. The only
    /// constraints that fail are the two equality constraints that tie the base of
    /// the first step to the `g_d` cells.
    #[test]
    fn a_different_base_in_the_chain_is_rejected() {
        use crate::backend::group::{Curve, GroupEncoding};
        use crate::backend::pasta_curves::arithmetic::CurveAffine;
        use crate::keys::DiversifiedTransmissionKey;

        use crate::backend::halo2_proofs::dev::VerifyFailure;

        let sk = SpendingKey::from_bytes([7; 32]).unwrap();
        let fvk = FullViewingKey::from(&sk);
        let address = fvk.address(Diversifier::from_bytes([3; 11]), Scope::External);
        let other_address = fvk.address(Diversifier::from_bytes([4; 11]), Scope::External);
        let alpha = SpendAuthRandomizer::from_bytes([1; 32]).unwrap();
        let (circuit, instance) = circuit_and_instance(&sk, &address, Scope::External, alpha);
        let run = |instance: &Instance| {
            MockProver::run(K, &circuit, vec![instance.to_halo2_instance().to_vec()])
                .unwrap()
                .verify()
        };

        let malicious_base = other_address.g_d().to_affine().coordinates().unwrap();
        fault::set_chain_base(Some((*malicious_base.x(), *malicious_base.y())));

        // The first run gives the point that the malicious chain computes.
        assert!(run(&instance).is_err());
        let (x, y) = fault::mul_result().unwrap();
        let claimed = pallas::Affine::from_xy(x, y).unwrap();
        assert_ne!(claimed.to_bytes(), instance.pk_d.to_bytes());
        let mut forged = instance.clone();
        forged.pk_d = DiversifiedTransmissionKey::from_bytes(&claimed.to_bytes()).unwrap();

        let failures = run(&forged).unwrap_err();
        fault::set_chain_base(None);
        assert!(!failures.is_empty());
        for failure in &failures {
            assert!(
                matches!(failure, VerifyFailure::Permutation { .. }),
                "unexpected failure: {failure}"
            );
        }
    }

    /// `ak` and `nk` that are not less than `2^254` take the canonicity branch of the
    /// `Commit^ivk` gates. A random key takes it with negligible probability.
    #[test]
    fn keys_above_two_pow_254_are_accepted() {
        use crate::backend::ff::{Field, PrimeField};
        use crate::backend::group::GroupEncoding;

        /// Length in bytes of `ak`, and of `nk`, in the raw encoding of a full
        /// viewing key.
        const KEY_LENGTH: usize = 32;
        /// The exponent of the smallest value with the top bit of a field element.
        const TOP_BIT: u64 = 254;

        let two_pow_254 = pallas::Base::from(2).pow_vartime([TOP_BIT]);
        let base_fvk = FullViewingKey::from(&SpendingKey::from_bytes([7; 32]).unwrap());
        let alpha = SpendAuthRandomizer::from_bytes([1; 32]).unwrap();

        // The first nk >= 2^254, and the first ak >= 2^254 that is the x-coordinate
        // of a point, for which the full viewing key is valid.
        let with_large_nk = (0u64..)
            .find_map(|offset| {
                let nk = two_pow_254 + pallas::Base::from(offset);
                let mut bytes = base_fvk.to_bytes();
                bytes[KEY_LENGTH..2 * KEY_LENGTH].copy_from_slice(&nk.to_repr());
                FullViewingKey::from_bytes(&bytes)
            })
            .unwrap();
        let with_large_ak = (0u64..)
            .find_map(|offset| {
                let ak = (two_pow_254 + pallas::Base::from(offset)).to_repr();
                Option::<pallas::Affine>::from(pallas::Affine::from_bytes(&ak))?;
                let mut bytes = base_fvk.to_bytes();
                bytes[..KEY_LENGTH].copy_from_slice(&ak);
                FullViewingKey::from_bytes(&bytes)
            })
            .unwrap();

        for fvk in [with_large_nk, with_large_ak] {
            let address = fvk.address(Diversifier::from_bytes([3; 11]), Scope::External);
            let ak = SpendValidatingKey::from(fvk.clone());
            let circuit = Circuit::new(
                &address,
                ak.clone(),
                alpha,
                *fvk.nk(),
                fvk.rivk(Scope::External),
            );
            let instance = Instance::new(&address, &ak.randomize(&alpha)).unwrap();
            assert!(accepts(&circuit, &instance));
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(CASES))]

        #[test]
        fn satisfied_only_by_the_statement(
            (sk, address, scope) in arb_key_and_address(),
            other_sk in arb_spending_key(),
            other_address in arb_address(),
            alpha in arb_spend_auth_randomizer(),
            other_alpha in arb_spend_auth_randomizer(),
        ) {
            prop_assume!(alpha != other_alpha);
            prop_assume!(address != other_address);
            let fvk = FullViewingKey::from(&sk);
            let other_fvk = FullViewingKey::from(&other_sk);
            let ak = spend_validating_key(&sk);
            let other_ak = spend_validating_key(&other_sk);

            let (circuit, instance) = circuit_and_instance(&sk, &address, scope, alpha);
            prop_assert!(accepts(&circuit, &instance));

            // A different rk in the primary input.
            let wrong_rk = Instance::new(&address, &ak.randomize(&other_alpha)).unwrap();
            prop_assert!(!accepts(&circuit, &wrong_rk));

            // A different address in the primary input.
            let wrong_address = Instance::new(&other_address, &ak.randomize(&alpha)).unwrap();
            prop_assert!(!accepts(&circuit, &wrong_address));

            // The right pk_d with the wrong g_d, and the reverse.
            let mut mixed = instance.clone();
            mixed.g_d = other_address.g_d();
            prop_assert!(!accepts(&circuit, &mixed));
            let mut mixed = instance.clone();
            mixed.pk_d = *other_address.pk_d();
            prop_assert!(!accepts(&circuit, &mixed));

            // The rivk of the other scope does not open the address's ivk.
            let (wrong_scope, _) = circuit_and_instance(&sk, &address, other_scope(scope), alpha);
            prop_assert!(!accepts(&wrong_scope, &instance));

            // The keys of a different wallet do not satisfy the statement for this
            // address, even with a matching rk.
            let (other_circuit, other_instance) =
                circuit_and_instance(&other_sk, &address, scope, alpha);
            prop_assert!(!accepts(&other_circuit, &other_instance));

            // One wrong key component in an otherwise correct witness, with the rk
            // that matches the witnessed ak.
            let wrong_nk = Circuit::new(&address, ak.clone(), alpha, *other_fvk.nk(), fvk.rivk(scope));
            prop_assert!(!accepts(&wrong_nk, &instance));
            let wrong_rivk =
                Circuit::new(&address, ak.clone(), alpha, *fvk.nk(), other_fvk.rivk(scope));
            prop_assert!(!accepts(&wrong_rivk, &instance));
            let wrong_ak =
                Circuit::new(&address, other_ak.clone(), alpha, *fvk.nk(), fvk.rivk(scope));
            let rk_of_wrong_ak = Instance::new(&address, &other_ak.randomize(&alpha)).unwrap();
            prop_assert!(!accepts(&wrong_ak, &rk_of_wrong_ak));
        }

        #[test]
        fn sampled_faults_are_rejected(
            (sk, address, scope) in arb_key_and_address(),
            alpha in arb_spend_auth_randomizer(),
            samples in prop::collection::vec(any::<prop::sample::Index>(), SAMPLED_FAULTS),
        ) {
            let (circuit, instance) = circuit_and_instance(&sk, &address, scope, alpha);
            let cells = witnessed_cells(&circuit, &instance);
            for sample in samples {
                let index = sample.index(cells.len());
                prop_assert!(
                    !accepts_fault(&circuit, &instance, index)
                        || FREE_AUXILIARY_CELLS.contains(&cells[index]),
                    "the circuit accepts a change of {:?}",
                    cells[index]
                );
            }
        }
    }
}
