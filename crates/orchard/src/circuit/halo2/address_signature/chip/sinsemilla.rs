//! Sinsemilla hashing and range checks of the narrow chip.
//!
//! The Sinsemilla constraints are those of `halo2_gadgets::sinsemilla::chip`. The
//! range checks have the semantics of
//! `halo2_gadgets::utilities::lookup_range_check`, but they use the lookup argument
//! of the Sinsemilla gate: a range-check row witnesses the coordinates of the
//! generator whose index is the word. The table has one row for each 10-bit index,
//! so the lookup constrains the word to 10 bits.

use alloc::vec::Vec;

use crate::backend::ff::{Field, PrimeField};
use crate::backend::halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::{ConstraintSystem, Constraints, Error, Expression},
};
use crate::backend::pasta_curves::{arithmetic::CurveAffine, pallas};
use crate::backend::sinsemilla::{K, SINSEMILLA_S};

use super::{Cell, Config, Point, assign, ecc::STEP_ROWS, nth};

/// Value of `f_s2` inside a piece, and on a running-sum range-check row.
const S2_RUNNING: u64 = 1;

/// Value of `f_s2` on the last word of a piece that is not the final piece, and on a
/// range-check row whose word is witnessed directly.
const S2_PIECE_END: u64 = 0;

/// Value of `f_s2` on the last word of the final piece.
const S2_FINAL: u64 = 2;

/// Index of the Lagrange column that holds `x_Q` on the first row of a hash.
const X_Q_COLUMN: usize = 0;

/// Index of the Lagrange column that holds `y_Q` on the first row of a hash.
const Y_Q_COLUMN: usize = 1;

/// Index of the Lagrange column that holds the shift factor of a short range check.
const SHIFT_COLUMN: usize = 0;

/// Index of the Lagrange column that holds the running-sum mode `f_s2` on a lookup
/// row.
///
/// On a Sinsemilla word: 1 inside a piece, 0 on the last word of a piece that is not
/// the final piece, 2 on the last word of the final piece. On a range-check row: 1
/// for a running-sum word, 0 for a word that is witnessed directly.
///
/// Each expression that reads this column has the lookup selector of its row as a
/// factor, so the Lagrange coefficients on fixed-base window rows have no effect.
const S2_COLUMN: usize = 2;

/// Value of the lookup selector on the first row of a Sinsemilla word.
const LOOKUP_SINSEMILLA: u64 = 1;

/// Value of the lookup selector on a range-check row.
const LOOKUP_RANGE_CHECK: u64 = 2;

/// A message piece: its value, and its length in `K`-bit words.
pub(super) struct Piece {
    pub(super) value: Value<pallas::Base>,
    pub(super) num_words: usize,
}

/// The little-endian `K`-bit words of the low `num_words * K` bits of `value`.
fn words(value: &pallas::Base, num_words: usize) -> Vec<usize> {
    let repr = value.to_repr();
    let bit = |i: usize| usize::from((repr[i / 8] >> (i % 8)) & 1);
    (0..num_words)
        .map(|word| (0..K).map(|i| bit(word * K + i) << i).sum())
        .collect()
}

/// The running sums `z_0 = value`, `z_{i+1} = (z_i - word_i) / 2^K`.
fn running_sums(value: &pallas::Base, words: &[usize]) -> Vec<pallas::Base> {
    let inv_two_pow_k = pallas::Base::from(1 << K).invert().unwrap();
    let mut sums = Vec::with_capacity(words.len() + 1);
    let mut z = *value;
    sums.push(z);
    for word in words {
        z = (z - pallas::Base::from(*word as u64)) * inv_two_pow_k;
        sums.push(z);
    }
    sums
}

/// The witness of a Sinsemilla hash.
struct HashWitness {
    /// `x_a` before each word, and after the last word.
    x_a: Vec<pallas::Base>,
    lambda_1: Vec<pallas::Base>,
    lambda_2: Vec<pallas::Base>,
    /// The running sum at each word.
    z: Vec<pallas::Base>,
    /// The `x`-coordinate of the generator of each word.
    x_p: Vec<pallas::Base>,
    /// `y_a` after the last word.
    y_final: pallas::Base,
}

impl HashWitness {
    /// Returns `None` if an incomplete addition has an exceptional case, which is the
    /// `⊥` output of the hash.
    fn new(q: pallas::Affine, pieces: &[(pallas::Base, usize)]) -> Option<Self> {
        let q = q.coordinates().expect("Q is not the identity");
        let (mut x_a, mut y_a) = (*q.x(), *q.y());
        let mut witness = HashWitness {
            x_a: vec![x_a],
            lambda_1: Vec::new(),
            lambda_2: Vec::new(),
            z: Vec::new(),
            x_p: Vec::new(),
            y_final: y_a,
        };
        for (value, num_words) in pieces {
            let words = words(value, *num_words);
            let sums = running_sums(value, &words);
            for (word, z) in words.iter().zip(sums) {
                let (x_p, y_p) = SINSEMILLA_S[*word];
                let lambda_1 = (y_a - y_p) * Option::<pallas::Base>::from((x_a - x_p).invert())?;
                let x_r = lambda_1.square() - x_a - x_p;
                let lambda_2 =
                    y_a.double() * Option::<pallas::Base>::from((x_a - x_r).invert())? - lambda_1;
                let x_a_next = lambda_2.square() - x_a - x_r;
                y_a = lambda_2 * (x_a - x_a_next) - y_a;
                x_a = x_a_next;

                witness.x_a.push(x_a);
                witness.lambda_1.push(lambda_1);
                witness.lambda_2.push(lambda_2);
                witness.z.push(z);
                witness.x_p.push(x_p);
            }
        }
        witness.y_final = y_a;
        Some(witness)
    }
}

impl Config {
    pub(super) fn create_sinsemilla_gates(&self, meta: &mut ConstraintSystem<pallas::Base>) {
        let two = pallas::Base::from(2);
        let two_pow_k = pallas::Base::from(1 << K);
        let next_step = STEP_ROWS as i32;

        // The two indicators of the lookup selector, which is 0, 1, or 2.
        // f_sin = f_lookup * (2 - f_lookup): 1 on a Sinsemilla word, else 0.
        let f_sin = |f_lookup: Expression<pallas::Base>| {
            f_lookup.clone() * (Expression::Constant(two) - f_lookup)
        };
        // f_rc = f_lookup * (f_lookup - 1) / 2: 1 on a range-check row, else 0.
        let f_rc = |f_lookup: Expression<pallas::Base>| {
            f_lookup.clone()
                * (f_lookup - Expression::Constant(pallas::Base::ONE))
                * pallas::Base::TWO_INV
        };

        // q_s3 = f_s2 * (f_s2 - 1): 2 on the last word of the final piece, else 0.
        let q_s3 = |f_s2: Expression<pallas::Base>| {
            f_s2.clone() * (f_s2 - Expression::Constant(pallas::Base::ONE))
        };

        // A Sinsemilla word is a double-and-add step:
        //
        // | x_a  | lambda_1  | lambda_2  |
        // | z    | x_p       |           |
        // | x_a' | lambda_1' | lambda_2' |
        // | z'   | x_p'      |           |
        //
        // A range-check row is:
        //
        // | z  | x | y |
        // | z' |   |   |
        //
        // https://p.z.cash/halo2-0.1:sinsemilla-constraints?partial
        // https://p.z.cash/halo2-0.1:decompose-combined-lookup
        meta.lookup(|meta| {
            let f_lookup = meta.query_fixed(self.f_lookup);
            let f_sin = f_sin(f_lookup.clone());
            let f_rc = f_rc(f_lookup);
            let f_s2 = meta.query_fixed(self.lagrange[S2_COLUMN]);
            // 1 if the word is the difference of two running sums, 0 if it is the
            // running sum itself.
            let q_run = f_s2.clone() - q_s3(f_s2);

            // m_{i+1} = z_{i} - 2^K * q_{run,i} * z_{i + 1}
            let sinsemilla_word =
                self.adv(meta, 0, 1) - q_run.clone() * self.adv(meta, 0, next_step + 1) * two_pow_k;
            let range_check_word = self.adv(meta, 0, 0) - q_run * self.adv(meta, 0, 1) * two_pow_k;

            let x_p = self.adv(meta, 1, 1);
            // y_{p,i} = (Y_{A,i} / 2) - lambda1 * (x_{A,i} - x_{P,i})
            let y_p = {
                let lambda_1 = self.adv(meta, 1, 0);
                let x_a = self.adv(meta, 0, 0);
                self.big_y_a(meta, 0) * pallas::Base::TWO_INV - lambda_1 * (x_a - x_p.clone())
            };

            // Lookup expressions default to the first entry when no selector is
            // enabled. The first table index is 0.
            let (init_x, init_y) = SINSEMILLA_S[0];
            let not_enabled =
                Expression::Constant(pallas::Base::ONE) - f_sin.clone() - f_rc.clone();
            let index = f_sin.clone() * sinsemilla_word + f_rc.clone() * range_check_word;
            let x = f_sin.clone() * x_p
                + f_rc.clone() * self.adv(meta, 1, 0)
                + not_enabled.clone() * init_x;
            let y = f_sin * y_p + f_rc * self.adv(meta, 2, 0) + not_enabled * init_y;

            vec![(index, self.table.0), (x, self.table.1), (y, self.table.2)]
        });

        // Check that the initial x_A is x_Q, and that the initial x_A, x_P, lambda_1,
        // lambda_2 are consistent with y_Q.
        //
        // https://p.z.cash/halo2-0.1:sinsemilla-constraints?partial
        meta.create_gate("Initial Q", |meta| {
            let q_sin_init = meta.query_selector(self.q_sin_init);
            let x_q = meta.query_fixed(self.lagrange[X_Q_COLUMN]);
            let y_q = meta.query_fixed(self.lagrange[Y_Q_COLUMN]);
            let init_x_q_check = self.adv(meta, 0, 0) - x_q;
            // 2 * y_q - Y_{A,0} = 0
            let init_y_q_check = y_q * two - self.big_y_a(meta, 0);
            Constraints::with_selector(
                q_sin_init,
                [
                    ("init_x_q_check", init_x_q_check),
                    ("init_y_q_check", init_y_q_check),
                ],
            )
        });

        // https://p.z.cash/halo2-0.1:sinsemilla-constraints?partial
        meta.create_gate("Sinsemilla gate", |meta| {
            let q_s1 = f_sin(meta.query_fixed(self.f_lookup));
            let q_s3 = q_s3(meta.query_fixed(self.lagrange[S2_COLUMN]));

            let lambda_1_next = self.adv(meta, 1, next_step);
            let lambda_2_cur = self.adv(meta, 2, 0);
            let x_a_cur = self.adv(meta, 0, 0);
            let x_a_next = self.adv(meta, 0, next_step);
            let x_r = self.x_r(meta, 0);
            let big_y_a_cur = self.big_y_a(meta, 0);
            let big_y_a_next = self.big_y_a(meta, next_step);

            // lambda2^2 - (x_a_next + x_r + x_a_cur) = 0
            let secant_line =
                lambda_2_cur.clone().square() - (x_a_next.clone() + x_r + x_a_cur.clone());

            // lhs - rhs = 0, where
            //    - lhs = 4 * lambda_2_cur * (x_a_cur - x_a_next)
            //    - rhs = (2 * Y_A_cur + (2 - q_s3) * Y_A_next + 2 * q_s3 * y_a_final)
            let y_check = {
                let lhs = lambda_2_cur * pallas::Base::from(4) * (x_a_cur - x_a_next);
                // y_a_final is in the lambda_1 cell of the row after the last word.
                let y_a_final = lambda_1_next;
                let rhs = big_y_a_cur * two
                    + (Expression::Constant(two) - q_s3.clone()) * big_y_a_next
                    + q_s3 * two * y_a_final;
                lhs - rhs
            };

            Constraints::with_selector(q_s1, [("Secant line", secant_line), ("y check", y_check)])
        });

        // | word                 |
        // | word * 2^(K - bits)  |
        //
        // https://p.z.cash/halo2-0.1:decompose-short-lookup
        meta.create_gate("Short lookup bitshift", |meta| {
            let q_shift = meta.query_selector(self.q_shift);
            let word = self.adv(meta, 0, 0);
            let shifted_word = self.adv(meta, 0, 1);
            let shift = meta.query_fixed(self.lagrange[SHIFT_COLUMN]);
            Constraints::with_selector(q_shift, Some(word * shift - shifted_word))
        });
    }

    /// Loads the Sinsemilla generator table.
    pub(in crate::circuit::halo2::address_signature) fn load_table(
        &self,
        layouter: &mut impl Layouter<pallas::Base>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "generator table",
            |mut table| {
                for (index, (x, y)) in SINSEMILLA_S.iter().enumerate() {
                    table.assign_cell(
                        || "index",
                        self.table.0,
                        index,
                        || Value::known(pallas::Base::from(index as u64)),
                    )?;
                    table.assign_cell(|| "x", self.table.1, index, || Value::known(*x))?;
                    table.assign_cell(|| "y", self.table.2, index, || Value::known(*y))?;
                }
                Ok(())
            },
        )
    }

    /// Hashes `pieces` to a point, starting from the public point `q`.
    ///
    /// Returns the point, and the running sums of each piece. The first running sum
    /// of a piece is the piece. Each piece is constrained to `num_words * K` bits.
    pub(super) fn hash_to_point(
        &self,
        mut layouter: impl Layouter<pallas::Base>,
        q: pallas::Affine,
        pieces: &[Piece],
    ) -> Result<(Point, Vec<Vec<Cell>>), Error> {
        let values = pieces.iter().fold(Value::known(Vec::new()), |acc, piece| {
            acc.zip(piece.value).map(|(mut acc, value)| {
                acc.push((value, piece.num_words));
                acc
            })
        });
        let witness = values.map(|values| HashWitness::new(q, &values));
        witness.error_if_known_and(|witness| witness.is_none())?;
        let witness = witness.map(|witness| witness.expect("checked above"));
        let witness = witness.as_ref();

        let q = q.coordinates().expect("Q is not the identity");
        let num_words: usize = pieces.iter().map(|piece| piece.num_words).sum();

        layouter.assign_region(
            || "Sinsemilla hash",
            |mut region| {
                super::enter("Sinsemilla hash");
                self.q_sin_init.enable(&mut region, 0)?;
                region.assign_fixed(
                    || "x_Q",
                    self.lagrange[X_Q_COLUMN],
                    0,
                    || Value::known(*q.x()),
                )?;
                region.assign_fixed(
                    || "y_Q",
                    self.lagrange[Y_Q_COLUMN],
                    0,
                    || Value::known(*q.y()),
                )?;

                let mut sums = Vec::with_capacity(pieces.len());
                let mut word = 0;
                for (index, piece) in pieces.iter().enumerate() {
                    let final_piece = index + 1 == pieces.len();
                    let mut piece_sums = Vec::with_capacity(piece.num_words);
                    for piece_word in 0..piece.num_words {
                        let row = word * STEP_ROWS;
                        let s2 = if piece_word + 1 < piece.num_words {
                            S2_RUNNING
                        } else if final_piece {
                            S2_FINAL
                        } else {
                            S2_PIECE_END
                        };
                        region.assign_fixed(
                            || "f_lookup",
                            self.f_lookup,
                            row,
                            || Value::known(pallas::Base::from(LOOKUP_SINSEMILLA)),
                        )?;
                        region.assign_fixed(
                            || "f_s2",
                            self.lagrange[S2_COLUMN],
                            row,
                            || Value::known(pallas::Base::from(s2)),
                        )?;

                        assign(&mut region, self.a[0], row, witness.map(|w| w.x_a[word]))?;
                        assign(
                            &mut region,
                            self.a[1],
                            row,
                            witness.map(|w| w.lambda_1[word]),
                        )?;
                        assign(
                            &mut region,
                            self.a[2],
                            row,
                            witness.map(|w| w.lambda_2[word]),
                        )?;
                        piece_sums.push(assign(
                            &mut region,
                            self.a[0],
                            row + 1,
                            witness.map(|w| w.z[word]),
                        )?);
                        assign(
                            &mut region,
                            self.a[1],
                            row + 1,
                            witness.map(|w| w.x_p[word]),
                        )?;
                        word += 1;
                    }
                    sums.push(piece_sums);
                }

                // The row after the last word holds the output point.
                let row = num_words * STEP_ROWS;
                let point = Point {
                    x: assign(
                        &mut region,
                        self.a[0],
                        row,
                        witness.map(|w| w.x_a[num_words]),
                    )?,
                    y: assign(&mut region, self.a[1], row, witness.map(|w| w.y_final))?,
                };
                // The gate and the lookup of the last word query these cells, with a
                // factor of zero. Their values do not matter.
                for (column, row) in [(2, row), (0, row + 1), (1, row + 1)] {
                    region.assign_advice(
                        || "unused",
                        self.a[column],
                        row,
                        || Value::known(pallas::Base::ZERO),
                    )?;
                }

                Ok((point, sums))
            },
        )
    }

    /// Witnesses `value` and decomposes its low `num_words * K` bits into `K`-bit
    /// words.
    ///
    /// Returns the running sums `z_0 = value` to `z_{num_words}`. The last running
    /// sum is not constrained here: it is zero if and only if `value` has at most
    /// `num_words * K` bits.
    pub(super) fn range_check(
        &self,
        mut layouter: impl Layouter<pallas::Base>,
        value: Value<pallas::Base>,
        num_words: usize,
    ) -> Result<Vec<Cell>, Error> {
        let words = value.map(|value| words(&value, num_words));
        let sums = value
            .zip(words.as_ref())
            .map(|(value, words)| running_sums(&value, words));
        let generator = |index: usize| words.as_ref().map(|words| SINSEMILLA_S[words[index]]);

        layouter.assign_region(
            || "range check",
            |mut region| {
                super::enter("range check");
                let mut cells = Vec::with_capacity(num_words + 1);
                for row in 0..num_words {
                    self.enable_range_check(&mut region, row, S2_RUNNING)?;
                    cells.push(assign(&mut region, self.a[0], row, nth(&sums, row))?);
                    assign(&mut region, self.a[1], row, generator(row).map(|g| g.0))?;
                    assign(&mut region, self.a[2], row, generator(row).map(|g| g.1))?;
                }
                cells.push(assign(
                    &mut region,
                    self.a[0],
                    num_words,
                    nth(&sums, num_words),
                )?);
                Ok(cells)
            },
        )
    }

    /// Witnesses `value` and constrains it to `num_bits` bits, where `num_bits` is
    /// less than `K`.
    ///
    /// The value and the value shifted left by `K - num_bits` bits are each looked
    /// up as a `K`-bit word.
    pub(super) fn range_check_short(
        &self,
        mut layouter: impl Layouter<pallas::Base>,
        value: Value<pallas::Base>,
        num_bits: usize,
    ) -> Result<Cell, Error> {
        assert!(num_bits < K);
        let shift = pallas::Base::from(1 << (K - num_bits));
        let shifted = value.map(|value| value * shift);
        let generator =
            |word: Value<pallas::Base>| word.map(|word| SINSEMILLA_S[words(&word, 1)[0]]);

        layouter.assign_region(
            || "short range check",
            |mut region| {
                super::enter("short range check");
                self.q_shift.enable(&mut region, 0)?;
                region.assign_fixed(
                    || "shift",
                    self.lagrange[SHIFT_COLUMN],
                    0,
                    || Value::known(shift),
                )?;
                let mut cell = None;
                for (row, word) in [value, shifted].into_iter().enumerate() {
                    self.enable_range_check(&mut region, row, S2_PIECE_END)?;
                    let word_cell = assign(&mut region, self.a[0], row, word)?;
                    assign(&mut region, self.a[1], row, generator(word).map(|g| g.0))?;
                    assign(&mut region, self.a[2], row, generator(word).map(|g| g.1))?;
                    cell.get_or_insert(word_cell);
                }
                Ok(cell.expect("there are two rows"))
            },
        )
    }

    fn enable_range_check(
        &self,
        region: &mut crate::backend::halo2_proofs::circuit::Region<'_, pallas::Base>,
        row: usize,
        s2: u64,
    ) -> Result<(), Error> {
        region.assign_fixed(
            || "f_lookup",
            self.f_lookup,
            row,
            || Value::known(pallas::Base::from(LOOKUP_RANGE_CHECK)),
        )?;
        region.assign_fixed(
            || "f_s2",
            self.lagrange[S2_COLUMN],
            row,
            || Value::known(pallas::Base::from(s2)),
        )?;
        Ok(())
    }
}
