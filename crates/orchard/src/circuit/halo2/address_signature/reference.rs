//! The address signature circuit on the Action circuit's chips.
//!
//! This is the statement of [`Circuit`] on the audited chips of `halo2_gadgets` and
//! the Orchard `Commit^ivk` chip. Tests use it as a reference: the narrow chip must
//! accept and reject the same statements.

use crate::backend::group::Curve;
use crate::backend::halo2_gadgets::{
    ecc::{
        CircuitVersion, FixedPoint, NonIdentityPoint, ScalarFixed, ScalarVar,
        chip::{EccChip, EccConfig},
    },
    sinsemilla::chip::{SinsemillaChip, SinsemillaConfig},
    utilities::lookup_range_check::{LookupRangeCheck, LookupRangeCheckConfig},
};
use crate::backend::halo2_proofs::{
    circuit::{Layouter, floor_planner},
    plonk::{self, Advice, Column, Instance as InstanceColumn},
};
use crate::backend::pasta_curves::pallas;

use super::{Circuit, G_D_X, G_D_Y, PK_D_X, PK_D_Y, RK_X, RK_Y};
use crate::circuit::halo2::{
    commit_ivk::{CommitIvkChip, CommitIvkConfig},
    gadget::{self, assign_free_advice},
};
use crate::constants::{
    OrchardCommitDomains, OrchardFixedBases, OrchardFixedBasesFull, OrchardHashDomains,
};

/// Number of advice columns. The ECC and `Commit^ivk` chips each span ten.
const ADVICE_COLUMNS: usize = 10;

/// Number of fixed columns that hold the fixed-base Lagrange coefficients.
const LAGRANGE_COEFF_COLUMNS: usize = 8;

/// Number of advice columns that one Sinsemilla chip uses.
const SINSEMILLA_ADVICE_COLUMNS: usize = 5;

/// Index of the advice column in which Sinsemilla message pieces are witnessed. It is
/// the column the Action circuit uses for its first Sinsemilla chip.
const SINSEMILLA_WITNESS_PIECES_COLUMN: usize = 6;

/// Index of the advice column that carries the running sums of all range checks. It
/// is the column the Action circuit uses.
const RANGE_CHECK_COLUMN: usize = 9;

/// Index of the advice column in which free private inputs are witnessed.
const FREE_ADVICE_COLUMN: usize = 0;

/// Configuration of the reference circuit.
#[derive(Clone, Debug)]
pub(crate) struct Config {
    primary: Column<InstanceColumn>,
    advices: [Column<Advice>; ADVICE_COLUMNS],
    ecc_config: EccConfig<OrchardFixedBases>,
    sinsemilla_config:
        SinsemillaConfig<OrchardHashDomains, OrchardCommitDomains, OrchardFixedBases>,
    commit_ivk_config: CommitIvkConfig,
}

/// The address signature circuit on the Action circuit's chips.
#[derive(Clone, Debug)]
pub(crate) struct ReferenceCircuit(pub(crate) Circuit);

impl plonk::Circuit<pallas::Base> for ReferenceCircuit {
    type Config = Config;
    type FloorPlanner = floor_planner::V1;

    fn without_witnesses(&self) -> Self {
        ReferenceCircuit(Circuit::empty())
    }

    fn configure(meta: &mut plonk::ConstraintSystem<pallas::Base>) -> Self::Config {
        let advices: [Column<Advice>; ADVICE_COLUMNS] =
            core::array::from_fn(|_| meta.advice_column());

        // Fixed columns for the Sinsemilla generator lookup table.
        let table_idx = meta.lookup_table_column();
        let lookup = (
            table_idx,
            meta.lookup_table_column(),
            meta.lookup_table_column(),
        );

        // Instance column used for public inputs.
        let primary = meta.instance_column();
        meta.enable_equality(primary);

        // Permutation over all advice columns.
        for advice in advices.iter() {
            meta.enable_equality(*advice);
        }

        let lagrange_coeffs: [_; LAGRANGE_COEFF_COLUMNS] =
            core::array::from_fn(|_| meta.fixed_column());

        // Use the first Lagrange coefficient column for loading global constants, as
        // the Action circuit does.
        meta.enable_constant(lagrange_coeffs[0]);

        let range_check =
            LookupRangeCheckConfig::configure(meta, advices[RANGE_CHECK_COLUMN], table_idx);

        // Configuration for curve point operations. This circuit does not use
        // fixed-base scalar multiplication by a short or a base-field scalar, so it
        // does not create those gates.
        let ecc_config = EccChip::<OrchardFixedBases>::configure_full_width_fixed_base_only(
            meta,
            advices,
            lagrange_coeffs,
            range_check,
        );

        // Configuration for the Sinsemilla hash inside Commit^ivk.
        let sinsemilla_config = SinsemillaChip::configure(
            meta,
            advices[..SINSEMILLA_ADVICE_COLUMNS]
                .try_into()
                .expect("the Sinsemilla chip uses five advice columns"),
            advices[SINSEMILLA_WITNESS_PIECES_COLUMN],
            lagrange_coeffs[0],
            lookup,
            range_check,
            false,
        );

        // Configuration to handle decomposition and canonicity checking for CommitIvk.
        let commit_ivk_config = CommitIvkChip::configure(meta, advices);

        Config {
            primary,
            advices,
            ecc_config,
            sinsemilla_config,
            commit_ivk_config,
        }
    }

    #[allow(non_snake_case)]
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<pallas::Base>,
    ) -> Result<(), plonk::Error> {
        let circuit = &self.0;
        // Load the Sinsemilla generator lookup table used by the whole circuit.
        SinsemillaChip::load(config.sinsemilla_config.clone(), &mut layouter)?;

        // The anchored version constrains the base of the variable-base scalar
        // multiplication to equal `g_d`. Without it, a prover could choose its own
        // base and satisfy diversified address integrity for any `pk_d`.
        let ecc_chip = EccChip::construct(config.ecc_config.clone(), CircuitVersion::AnchoredBase);

        // Witness g_d and bind it to the primary input.
        let g_d = NonIdentityPoint::new(
            ecc_chip.clone(),
            layouter.namespace(|| "witness g_d"),
            circuit.g_d.as_ref().map(|g_d| g_d.to_affine()),
        )?;
        layouter.constrain_instance(g_d.inner().x().cell(), config.primary, G_D_X)?;
        layouter.constrain_instance(g_d.inner().y().cell(), config.primary, G_D_Y)?;

        // Witness ak_P.
        let ak_P = NonIdentityPoint::new(
            ecc_chip.clone(),
            layouter.namespace(|| "witness ak_P"),
            circuit.ak.as_ref().map(|ak| ak.to_point().to_affine()),
        )?;

        // Witness nk.
        let nk = assign_free_advice(
            layouter.namespace(|| "witness nk"),
            config.advices[FREE_ADVICE_COLUMN],
            circuit.nk.map(|nk| nk.inner()),
        )?;

        // Spend authority (https://p.z.cash/ZKS:action-spend-authority)
        {
            let alpha = ScalarFixed::new(
                ecc_chip.clone(),
                layouter.namespace(|| "alpha"),
                circuit.alpha,
            )?;

            // alpha_commitment = [alpha] SpendAuthG
            let (alpha_commitment, _) = {
                let spend_auth_g = OrchardFixedBasesFull::SpendAuthG;
                let spend_auth_g = FixedPoint::from_inner(ecc_chip.clone(), spend_auth_g);
                spend_auth_g.mul(layouter.namespace(|| "[alpha] SpendAuthG"), alpha)?
            };

            // [alpha] SpendAuthG + ak_P
            let rk = alpha_commitment.add(layouter.namespace(|| "rk"), &ak_P)?;

            // Constrain rk to equal public input
            layouter.constrain_instance(rk.inner().x().cell(), config.primary, RK_X)?;
            layouter.constrain_instance(rk.inner().y().cell(), config.primary, RK_Y)?;
        }

        // Diversified address integrity (https://p.z.cash/ZKS:action-addr-integrity?partial).
        {
            let ivk = {
                let ak = ak_P.extract_p().inner().clone();
                let rivk = ScalarFixed::new(
                    ecc_chip.clone(),
                    layouter.namespace(|| "rivk"),
                    circuit.rivk.map(|rivk| rivk.inner()),
                )?;

                gadget::commit_ivk(
                    SinsemillaChip::construct(config.sinsemilla_config.clone()),
                    ecc_chip.clone(),
                    CommitIvkChip::construct(config.commit_ivk_config.clone()),
                    layouter.namespace(|| "CommitIvk"),
                    ak,
                    nk,
                    rivk,
                )?
            };
            let ivk =
                ScalarVar::from_base(ecc_chip.clone(), layouter.namespace(|| "ivk"), ivk.inner())?;

            // [ivk] g_d
            // The scalar value is passed through and discarded.
            let (derived_pk_d, _ivk) = g_d.mul(layouter.namespace(|| "[ivk] g_d"), ivk)?;

            // Witness pk_d as a non-identity point, constrain it to equal the derived
            // point, and bind it to the primary input.
            let pk_d = NonIdentityPoint::new(
                ecc_chip,
                layouter.namespace(|| "witness pk_d"),
                circuit.pk_d.map(|pk_d| pk_d.inner().to_affine()),
            )?;
            derived_pk_d.constrain_equal(layouter.namespace(|| "pk_d equality"), &pk_d)?;
            layouter.constrain_instance(pk_d.inner().x().cell(), config.primary, PK_D_X)?;
            layouter.constrain_instance(pk_d.inner().y().cell(), config.primary, PK_D_Y)?;
        }

        Ok(())
    }
}
