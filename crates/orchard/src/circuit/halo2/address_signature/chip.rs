//! A narrow chip for the address signature circuit.
//!
//! The Action circuit's chips use ten advice columns and two lookup arguments. A
//! Halo 2 proof contains one commitment for each advice column, one evaluation for
//! each queried cell position, and a fixed number of elements for each lookup
//! argument. This chip enforces the same constraint equations in three advice
//! columns and one lookup argument, so the proof is smaller. It uses more rows, which
//! do not change the proof size.
//!
//! # Relation to the Action circuit's chips
//!
//! Each gate here has the polynomial constraints of a gate in `halo2_gadgets` or in
//! the Orchard `Commit^ivk` chip. Only the positions of the cells differ. The
//! differences in structure are:
//!
//! - A gate reads cells from up to five consecutive rows, because a row holds three
//!   cells.
//! - Variable-base scalar multiplication runs its incomplete additions as one chain.
//!   The Action circuit splits them into two halves that run side by side.
//! - Range checks look up `(word, x, y)` in the Sinsemilla generator table, with `x`
//!   and `y` witnessed, in place of a second lookup argument on the index column.
//! - Constants are enforced by gates and fixed columns. No fixed column is part of
//!   the permutation argument.
//!
//! This code has not had an independent audit.

use alloc::vec::Vec;

use crate::backend::halo2_gadgets::ecc::chip::H;
use crate::backend::halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, Value},
    plonk::{
        Advice, Column, ConstraintSystem, Error, Fixed, Instance as InstanceColumn, Selector,
        TableColumn,
    },
};
use crate::backend::pasta_curves::pallas;

mod commit_ivk;
mod ecc;
mod sinsemilla;

pub(super) use ecc::Point;

/// Number of advice columns.
pub(super) const ADVICE_COLUMNS: usize = 3;

/// A cell that holds a base field element.
pub(super) type Cell = AssignedCell<pallas::Base, pallas::Base>;

/// Configuration of the narrow chip.
#[derive(Clone, Debug)]
pub(crate) struct Config {
    /// The public inputs.
    pub(super) primary: Column<InstanceColumn>,
    /// The advice columns.
    a: [Column<Advice>; ADVICE_COLUMNS],
    /// Lagrange interpolation coefficients of a fixed-base window.
    ///
    /// The fixed-base window gate is the only gate that reads all of these columns,
    /// and it is active on window rows only. On other rows, some of these columns
    /// hold data for other gates: the coordinates of the Sinsemilla initial point,
    /// the shift factor of a short range check, and the running-sum mode of a
    /// lookup row. Each of those gates reads the data only under its own selector.
    lagrange: [Column<Fixed>; H],
    /// `z + 1` on the first row of a fixed-base window, where `z` is the `z` value
    /// of the window, and 0 on all other rows. It is not zero on a window row, so it
    /// is also the selector of the fixed-base window gate.
    fixed_z_plus_one: Column<Fixed>,
    /// The lookup selector: 1 on the first row of each Sinsemilla word, 2 on each
    /// range-check row, and 0 on all other rows.
    f_lookup: Column<Fixed>,
    /// The Sinsemilla generator table `(index, x, y)`.
    table: (TableColumn, TableColumn, TableColumn),

    /// Witnessed non-identity point.
    q_point: Selector,
    /// Complete addition.
    q_add: Selector,
    /// Fixed-base window: incomplete addition into the accumulator.
    q_fixed_add: Selector,
    /// Variable-base incomplete chain: initial row.
    q_mul_1: Selector,
    /// Variable-base incomplete chain: main loop.
    q_mul_2: Selector,
    /// Variable-base incomplete chain: last bit.
    q_mul_3: Selector,
    /// Variable-base complete bits: decomposition and conditional negation.
    q_mul_complete: Selector,
    /// Variable-base least significant bit.
    q_mul_lsb: Selector,
    /// Variable-base overflow check.
    q_mul_overflow: Selector,
    /// Sinsemilla initial point.
    q_sin_init: Selector,
    /// Short range check shift.
    q_shift: Selector,
    /// `Commit^ivk` canonicity of `ak`.
    q_commit_ivk_ak: Selector,
    /// `Commit^ivk` canonicity of `nk`.
    q_commit_ivk_nk: Selector,
}

impl Config {
    /// Creates the columns and all gates.
    pub(super) fn configure(meta: &mut ConstraintSystem<pallas::Base>) -> Self {
        let a: [Column<Advice>; ADVICE_COLUMNS] = core::array::from_fn(|_| meta.advice_column());
        for column in a.iter() {
            meta.enable_equality(*column);
        }
        fault::register(a);
        let primary = meta.instance_column();
        meta.enable_equality(primary);

        let config = Config {
            primary,
            a,
            lagrange: core::array::from_fn(|_| meta.fixed_column()),
            fixed_z_plus_one: meta.fixed_column(),
            f_lookup: meta.fixed_column(),
            table: (
                meta.lookup_table_column(),
                meta.lookup_table_column(),
                meta.lookup_table_column(),
            ),
            q_point: meta.selector(),
            q_add: meta.selector(),
            q_fixed_add: meta.selector(),
            q_mul_1: meta.selector(),
            q_mul_2: meta.selector(),
            q_mul_3: meta.selector(),
            q_mul_complete: meta.selector(),
            q_mul_lsb: meta.selector(),
            q_mul_overflow: meta.selector(),
            q_sin_init: meta.selector(),
            q_shift: meta.selector(),
            q_commit_ivk_ak: meta.selector(),
            q_commit_ivk_nk: meta.selector(),
        };

        config.create_ecc_gates(meta);
        config.create_sinsemilla_gates(meta);
        config.create_commit_ivk_gates(meta);

        config
    }

    /// Binds a cell to a row of the public input.
    pub(super) fn constrain_instance(
        &self,
        layouter: &mut impl Layouter<pallas::Base>,
        cell: &Cell,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.primary, row)
    }
}

/// Names the region whose cells are assigned next, for the fault test.
fn enter(name: &'static str) {
    fault::enter(name);
}

/// Assigns a witnessed value to an advice cell.
fn assign(
    region: &mut Region<'_, pallas::Base>,
    column: Column<Advice>,
    row: usize,
    value: Value<pallas::Base>,
) -> Result<Cell, Error> {
    region.assign_advice(
        || "witness",
        column,
        row,
        || fault::apply(column, row, value),
    )
}

/// Assigns a cell that is constrained to equal `cell`.
fn copy(
    region: &mut Region<'_, pallas::Base>,
    cell: &Cell,
    column: Column<Advice>,
    row: usize,
) -> Result<Cell, Error> {
    cell.copy_advice(|| "copy", region, column, row)
}

/// Assigns a cell with `value`, and constrains it to equal `cell`.
///
/// This is [`copy`], with the value given by the caller. The value is the value of
/// `cell`, except in a test that builds the witness of a dishonest prover: the
/// equality constraint must then reject the witness.
fn copy_with_value(
    region: &mut Region<'_, pallas::Base>,
    cell: &Cell,
    column: Column<Advice>,
    row: usize,
    value: Value<pallas::Base>,
) -> Result<Cell, Error> {
    let assigned = region.assign_advice(|| "copy", column, row, || value)?;
    region.constrain_equal(assigned.cell(), cell.cell())?;
    Ok(assigned)
}

/// Takes element `index` of a witness vector.
fn nth(values: &Value<Vec<pallas::Base>>, index: usize) -> Value<pallas::Base> {
    values.as_ref().map(|values| values[index])
}

/// Changes one witnessed cell, so that a test can show that each cell is constrained.
#[cfg(test)]
pub(super) mod fault {
    use alloc::vec::Vec;
    use core::cell::{Cell, RefCell};

    use super::ADVICE_COLUMNS;
    use crate::backend::ff::Field;
    use crate::backend::halo2_proofs::{
        circuit::Value,
        plonk::{Advice, Column},
    };
    use crate::backend::pasta_curves::pallas;

    /// The position of a witnessed cell: region name, column index, and row in the
    /// region.
    pub(in crate::circuit::halo2::address_signature) type Position = (&'static str, usize, usize);

    std::thread_local! {
        /// The witnessed cells that were assigned since the last reset.
        static ASSIGNED: RefCell<Vec<Position>> = const { RefCell::new(Vec::new()) };
        /// Index of the witnessed cell to change.
        static TARGET: Cell<Option<usize>> = const { Cell::new(None) };
        /// Name of the current region.
        static REGION: Cell<&'static str> = const { Cell::new("") };
        /// A base for the incomplete chain that replaces the real base.
        static CHAIN_BASE: Cell<Option<(pallas::Base, pallas::Base)>> = const { Cell::new(None) };
        /// The result of the last variable-base scalar multiplication.
        static MUL_RESULT: Cell<Option<(pallas::Base, pallas::Base)>> = const { Cell::new(None) };
        /// The advice columns of the chip that was configured last.
        static COLUMNS: Cell<Option<[Column<Advice>; ADVICE_COLUMNS]>> = const { Cell::new(None) };
    }

    pub(super) fn register(columns: [Column<Advice>; ADVICE_COLUMNS]) {
        COLUMNS.with(|cell| cell.set(Some(columns)));
    }

    /// Selects the cell to change in the next synthesis, and resets the record.
    pub(in crate::circuit::halo2::address_signature) fn set_target(target: Option<usize>) {
        ASSIGNED.with(|assigned| assigned.borrow_mut().clear());
        TARGET.with(|cell| cell.set(target));
    }

    /// The witnessed cells that were assigned since the last reset.
    pub(in crate::circuit::halo2::address_signature) fn assigned() -> Vec<Position> {
        ASSIGNED.with(|assigned| assigned.borrow().clone())
    }

    pub(super) fn enter(name: &'static str) {
        REGION.with(|region| region.set(name));
    }

    /// Makes the next syntheses use `base` as the base of the incomplete chain of
    /// variable-base scalar multiplication, in place of the real base. All other
    /// cells stay consistent with that chain. This is the witness of a prover that
    /// tries to use its own base.
    pub(in crate::circuit::halo2::address_signature) fn set_chain_base(
        base: Option<(pallas::Base, pallas::Base)>,
    ) {
        CHAIN_BASE.with(|cell| cell.set(base));
    }

    /// The result of the last variable-base scalar multiplication.
    pub(in crate::circuit::halo2::address_signature) fn mul_result()
    -> Option<(pallas::Base, pallas::Base)> {
        MUL_RESULT.with(Cell::get)
    }

    pub(super) fn chain_base(
        real: Value<(pallas::Base, pallas::Base)>,
    ) -> Value<(pallas::Base, pallas::Base)> {
        match CHAIN_BASE.with(Cell::get) {
            Some(base) => real.map(|_| base),
            None => real,
        }
    }

    pub(super) fn record_mul_result(result: Value<(pallas::Base, pallas::Base)>) {
        result.map(|result| MUL_RESULT.with(|cell| cell.set(Some(result))));
    }

    pub(super) fn apply(
        column: Column<Advice>,
        row: usize,
        value: Value<pallas::Base>,
    ) -> Value<pallas::Base> {
        let column = COLUMNS
            .with(Cell::get)
            .and_then(|columns| columns.iter().position(|c| *c == column))
            .expect("the chip is configured before it is synthesized");
        let index = ASSIGNED.with(|assigned| {
            let mut assigned = assigned.borrow_mut();
            assigned.push((REGION.with(Cell::get), column, row));
            assigned.len() - 1
        });
        if TARGET.with(Cell::get) == Some(index) {
            value.map(|value| value + pallas::Base::ONE)
        } else {
            value
        }
    }
}

#[cfg(not(test))]
mod fault {
    use super::ADVICE_COLUMNS;
    use crate::backend::halo2_proofs::{
        circuit::Value,
        plonk::{Advice, Column},
    };
    use crate::backend::pasta_curves::pallas;

    pub(super) fn register(_columns: [Column<Advice>; ADVICE_COLUMNS]) {}

    pub(super) fn enter(_name: &'static str) {}

    pub(super) fn chain_base(
        real: Value<(pallas::Base, pallas::Base)>,
    ) -> Value<(pallas::Base, pallas::Base)> {
        real
    }

    pub(super) fn record_mul_result(_result: Value<(pallas::Base, pallas::Base)>) {}

    pub(super) fn apply(
        _column: Column<Advice>,
        _row: usize,
        value: Value<pallas::Base>,
    ) -> Value<pallas::Base> {
        value
    }
}
