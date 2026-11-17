//! Elliptic curve operations of the narrow chip.
//!
//! The constraints are those of `halo2_gadgets::ecc::chip`. Each gate documents the
//! positions of its cells as `(column, row)`, with the row relative to the row on
//! which the selector is enabled.

use alloc::vec::Vec;

use crate::backend::ff::{Field, PrimeField};
use crate::backend::group::{Curve, CurveAffine as _, Group};
use crate::backend::halo2_gadgets::{
    ecc::chip::{FixedPoint, H, NUM_WINDOWS},
    utilities::{bool_check, range_check, ternary},
};
use crate::backend::halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::{ConstraintSystem, Constraints, Error, Expression, VirtualCells},
    poly::Rotation,
};
use crate::backend::pasta_curves::{arithmetic::CurveAffine, pallas};

use super::{Cell, Config, assign, copy, copy_with_value};
use crate::constants::{OrchardFixedBasesFull, T_Q};

/// Number of bits in a fixed-base window.
const WINDOW_BITS: usize = 3;

/// Number of bits of the variable-base scalar. It is the bit length of the Pallas
/// scalar field.
const SCALAR_BITS: usize = pallas::Scalar::NUM_BITS as usize;

/// Number of bits, after the incomplete additions, for which variable-base scalar
/// multiplication uses complete addition. The least significant bit is not one of
/// them.
const COMPLETE_BITS: usize = 3;

/// Number of bits for which variable-base scalar multiplication uses incomplete
/// addition: `k_254` to `k_4`.
const INCOMPLETE_BITS: usize = SCALAR_BITS - 1 - COMPLETE_BITS;

/// Number of most significant bits after which the running sum is `z_130`.
const BITS_TO_Z_130: usize = SCALAR_BITS - 130;

/// Number of rows of one step of a chain: a fixed-base window, a variable-base bit,
/// or a Sinsemilla word.
pub(super) const STEP_ROWS: usize = 2;

/// Number of 10-bit words in the low 130 bits of `s` in the overflow check.
const OVERFLOW_WORDS: usize = 13;

/// A point in affine coordinates. The identity is `(0, 0)`.
#[derive(Clone, Debug)]
pub(in crate::circuit::halo2::address_signature) struct Point {
    pub(in crate::circuit::halo2::address_signature) x: Cell,
    pub(in crate::circuit::halo2::address_signature) y: Cell,
}

impl Point {
    fn value(&self) -> Value<(pallas::Base, pallas::Base)> {
        self.x.value().copied().zip(self.y.value().copied())
    }
}

/// `inv0(x)`: the inverse of `x`, or zero if `x` is zero.
fn inv0(x: pallas::Base) -> pallas::Base {
    x.invert().unwrap_or(pallas::Base::ZERO)
}

/// The witness of one complete addition.
struct AddWitness {
    lambda: pallas::Base,
    alpha: pallas::Base,
    beta: pallas::Base,
    gamma: pallas::Base,
    delta: pallas::Base,
    x_r: pallas::Base,
    y_r: pallas::Base,
}

impl AddWitness {
    fn new(
        (x_p, y_p): (pallas::Base, pallas::Base),
        (x_q, y_q): (pallas::Base, pallas::Base),
    ) -> Self {
        let zero = pallas::Base::ZERO;
        let alpha = inv0(x_q - x_p);
        let beta = inv0(x_p);
        let gamma = inv0(x_q);
        let delta = if x_q == x_p { inv0(y_q + y_p) } else { zero };
        let lambda = if x_q != x_p {
            (y_q - y_p) * alpha
        } else if y_p != zero {
            x_p.square() * pallas::Base::from(3) * inv0(y_p.double())
        } else {
            zero
        };
        let (x_r, y_r) = if x_p == zero {
            (x_q, y_q)
        } else if x_q == zero {
            (x_p, y_p)
        } else if x_q == x_p && y_q == -y_p {
            (zero, zero)
        } else {
            let x_r = lambda.square() - x_p - x_q;
            (x_r, lambda * (x_p - x_r) - y_p)
        };
        AddWitness {
            lambda,
            alpha,
            beta,
            gamma,
            delta,
            x_r,
            y_r,
        }
    }
}

/// The witness of the incomplete additions of a fixed-base scalar multiplication.
struct FixedWitness {
    /// The window values.
    windows: Vec<pallas::Base>,
    /// The `u` value of each window point.
    us: Vec<pallas::Base>,
    /// The coordinates of each window point.
    points: Vec<(pallas::Base, pallas::Base)>,
    /// The accumulator before each window point is added. Entry 0 is not used.
    accumulators: Vec<(pallas::Base, pallas::Base)>,
}

impl FixedWitness {
    fn new(base: &OrchardFixedBasesFull, scalar: &pallas::Scalar) -> Self {
        let repr = scalar.to_repr();
        let bit = |i: usize| (repr[i / 8] >> (i % 8)) & 1;
        let windows: Vec<usize> = (0..NUM_WINDOWS)
            .map(|window| {
                (0..WINDOW_BITS)
                    .map(|i| usize::from(bit(window * WINDOW_BITS + i)) << i)
                    .sum()
            })
            .collect();

        // Window `w` selects `[(k_w + 2) * 8^w] B`. The last window selects
        // `[k_w * 8^w - sum_{j < w} 2 * 8^j] B`, which removes the offsets.
        let generator = base.generator().to_curve();
        let h = pallas::Scalar::from(H as u64);
        let two = pallas::Scalar::from(2);
        let mut power = pallas::Scalar::ONE;
        let mut offset = pallas::Scalar::ZERO;
        let mut projective = Vec::with_capacity(NUM_WINDOWS);
        for (window, k) in windows.iter().enumerate() {
            let k = pallas::Scalar::from(*k as u64);
            let multiple = if window + 1 < NUM_WINDOWS {
                (k + two) * power
            } else {
                k * power - offset
            };
            projective.push(generator * multiple);
            offset += two * power;
            power *= h;
        }

        let mut accumulators = Vec::with_capacity(NUM_WINDOWS);
        let mut accumulator = pallas::Point::identity();
        for point in &projective {
            accumulators.push(accumulator);
            accumulator += point;
        }

        let coordinates = |points: &[pallas::Point]| -> Vec<(pallas::Base, pallas::Base)> {
            let mut affine = vec![pallas::Affine::default(); points.len()];
            pallas::Point::batch_normalize(points, &mut affine);
            affine
                .iter()
                .map(|point| {
                    Option::from(point.coordinates())
                        .map(
                            |c: crate::backend::pasta_curves::arithmetic::Coordinates<_>| {
                                (*c.x(), *c.y())
                            },
                        )
                        .unwrap_or((pallas::Base::ZERO, pallas::Base::ZERO))
                })
                .collect()
        };

        let us = base.u();
        FixedWitness {
            us: windows
                .iter()
                .enumerate()
                .map(|(window, k)| {
                    pallas::Base::from_repr(us[window][*k]).expect("u is a field element")
                })
                .collect(),
            windows: windows
                .iter()
                .map(|k| pallas::Base::from(*k as u64))
                .collect(),
            points: coordinates(&projective),
            accumulators: coordinates(&accumulators),
        }
    }
}

/// The little-endian bits of `scalar + t_q`, computed over the integers.
///
/// Variable-base scalar multiplication uses `k = scalar + t_q`, where the Pallas scalar
/// field order is `2^254 + t_q`.
fn scalar_mul_bits(scalar: &pallas::Base) -> Vec<bool> {
    let mut k = [0u64; 4];
    for (limb, chunk) in k.iter_mut().zip(scalar.to_repr().chunks(8)) {
        *limb = u64::from_le_bytes(chunk.try_into().expect("a limb is eight bytes"));
    }
    let t_q = [T_Q as u64, (T_Q >> 64) as u64, 0, 0];
    let mut carry = 0u128;
    for (limb, t_q_limb) in k.iter_mut().zip(t_q) {
        let sum = u128::from(*limb) + u128::from(t_q_limb) + carry;
        *limb = sum as u64;
        carry = sum >> 64;
    }
    k.into_iter()
        .flat_map(u64::to_le_bytes)
        .flat_map(|byte| (0..8).map(move |shift| (byte >> shift) & 1 == 1))
        .take(SCALAR_BITS)
        .collect()
}

/// The witness of the incomplete additions of a variable-base scalar multiplication.
struct IncompleteWitness {
    /// `x_a` before each bit, and after the last bit.
    x_a: Vec<pallas::Base>,
    lambda_1: Vec<pallas::Base>,
    lambda_2: Vec<pallas::Base>,
    /// The running sum after each bit.
    z: Vec<pallas::Base>,
    /// `y_a` after the last bit.
    y_final: pallas::Base,
}

impl IncompleteWitness {
    /// Returns `None` if an incomplete addition has an exceptional case.
    fn new(
        (x_p, y_p): (pallas::Base, pallas::Base),
        (mut x_a, mut y_a): (pallas::Base, pallas::Base),
        bits: &[bool],
    ) -> Option<Self> {
        let mut witness = IncompleteWitness {
            x_a: vec![x_a],
            lambda_1: Vec::with_capacity(bits.len()),
            lambda_2: Vec::with_capacity(bits.len()),
            z: Vec::with_capacity(bits.len()),
            y_final: y_a,
        };
        let mut z = pallas::Base::ZERO;
        for bit in bits {
            let y_p = if *bit { y_p } else { -y_p };
            let lambda_1 = (y_a - y_p) * Option::<pallas::Base>::from((x_a - x_p).invert())?;
            let x_r = lambda_1.square() - x_a - x_p;
            let lambda_2 =
                y_a.double() * Option::<pallas::Base>::from((x_a - x_r).invert())? - lambda_1;
            let x_a_next = lambda_2.square() - x_a - x_r;
            y_a = lambda_2 * (x_a - x_a_next) - y_a;
            x_a = x_a_next;
            z = z.double() + pallas::Base::from(u64::from(*bit));

            witness.x_a.push(x_a);
            witness.lambda_1.push(lambda_1);
            witness.lambda_2.push(lambda_2);
            witness.z.push(z);
        }
        witness.y_final = y_a;
        Some(witness)
    }
}

impl Config {
    /// The cell at `(column, row)`, with the row relative to the current row.
    pub(super) fn adv(
        &self,
        meta: &mut VirtualCells<'_, pallas::Base>,
        column: usize,
        row: i32,
    ) -> Expression<pallas::Base> {
        meta.query_advice(self.a[column], Rotation(row))
    }

    /// `x_r = lambda_1^2 - x_a - x_p` of the double-and-add step that starts at `row`.
    ///
    /// A step holds `x_a`, `lambda_1`, `lambda_2` on its first row, and `x_p` in
    /// column 1 of its second row.
    pub(super) fn x_r(
        &self,
        meta: &mut VirtualCells<'_, pallas::Base>,
        row: i32,
    ) -> Expression<pallas::Base> {
        let x_a = self.adv(meta, 0, row);
        let lambda_1 = self.adv(meta, 1, row);
        let x_p = self.adv(meta, 1, row + 1);
        lambda_1.square() - x_a - x_p
    }

    /// `Y_A = (lambda_1 + lambda_2) * (x_a - x_r)` of the double-and-add step that
    /// starts at `row`. This is twice the `y`-coordinate of the accumulator.
    pub(super) fn big_y_a(
        &self,
        meta: &mut VirtualCells<'_, pallas::Base>,
        row: i32,
    ) -> Expression<pallas::Base> {
        let x_a = self.adv(meta, 0, row);
        let lambda_1 = self.adv(meta, 1, row);
        let lambda_2 = self.adv(meta, 2, row);
        (lambda_1 + lambda_2) * (x_a - self.x_r(meta, row))
    }

    pub(super) fn create_ecc_gates(&self, meta: &mut ConstraintSystem<pallas::Base>) {
        let one = Expression::Constant(pallas::Base::ONE);
        let curve_b = Expression::Constant(pallas::Affine::b());
        let next_step = STEP_ROWS as i32;

        // | x | y |   |
        //
        // https://p.z.cash/halo2-0.1:ecc-witness-non-identity-point
        meta.create_gate("witness non-identity point", |meta| {
            let q_point = meta.query_selector(self.q_point);
            let x = self.adv(meta, 0, 0);
            let y = self.adv(meta, 1, 0);
            let on_curve = y.square() - x.clone().square() * x - curve_b.clone();
            Constraints::with_selector(q_point, Some(("on_curve", on_curve)))
        });

        // | x_p   | y_p   | lambda |
        // | x_q   | y_q   | alpha  |
        // | x_r   | y_r   | beta   |
        // | gamma | delta |        |
        //
        // https://p.z.cash/halo2-0.1:ecc-complete-addition
        meta.create_gate("complete addition", |meta| {
            let q_add = meta.query_selector(self.q_add);
            let x_p = self.adv(meta, 0, 0);
            let y_p = self.adv(meta, 1, 0);
            let lambda = self.adv(meta, 2, 0);
            let x_q = self.adv(meta, 0, 1);
            let y_q = self.adv(meta, 1, 1);
            // alpha = inv0(x_q - x_p)
            let alpha = self.adv(meta, 2, 1);
            let x_r = self.adv(meta, 0, 2);
            let y_r = self.adv(meta, 1, 2);
            // beta = inv0(x_p)
            let beta = self.adv(meta, 2, 2);
            // gamma = inv0(x_q)
            let gamma = self.adv(meta, 0, 3);
            // delta = inv0(y_p + y_q) if x_q = x_p, 0 otherwise
            let delta = self.adv(meta, 1, 3);

            let x_q_minus_x_p = x_q.clone() - x_p.clone();
            let x_p_minus_x_r = x_p.clone() - x_r.clone();
            let y_q_plus_y_p = y_q.clone() + y_p.clone();
            let if_alpha = x_q_minus_x_p.clone() * alpha;
            let if_beta = x_p.clone() * beta;
            let if_gamma = x_q.clone() * gamma;
            let if_delta = y_q_plus_y_p.clone() * delta;

            let two = Expression::Constant(pallas::Base::from(2));
            let three = Expression::Constant(pallas::Base::from(3));

            // (x_q − x_p)⋅((x_q − x_p)⋅λ − (y_q−y_p)) = 0
            let poly1 = x_q_minus_x_p.clone()
                * (x_q_minus_x_p.clone() * lambda.clone() - (y_q.clone() - y_p.clone()));

            // (1 - (x_q - x_p)⋅α)⋅(2y_p ⋅λ - 3x_p^2) = 0
            let poly2 = (one.clone() - if_alpha.clone())
                * (two * y_p.clone() * lambda.clone() - three * x_p.clone().square());

            // (λ^2 - x_p - x_q - x_r)
            let nonexceptional_x_r =
                lambda.clone().square() - x_p.clone() - x_q.clone() - x_r.clone();
            // (λ ⋅(x_p - x_r) - y_p - y_r)
            let nonexceptional_y_r = lambda * x_p_minus_x_r - y_p.clone() - y_r.clone();

            // x_p⋅x_q⋅(x_q - x_p)⋅(λ^2 - x_p - x_q - x_r) = 0
            let poly3a =
                x_p.clone() * x_q.clone() * x_q_minus_x_p.clone() * nonexceptional_x_r.clone();
            // x_p⋅x_q⋅(x_q - x_p)⋅(λ ⋅(x_p - x_r) - y_p - y_r) = 0
            let poly3b = x_p.clone() * x_q.clone() * x_q_minus_x_p * nonexceptional_y_r.clone();
            // x_p⋅x_q⋅(y_q + y_p)⋅(λ^2 - x_p - x_q - x_r) = 0
            let poly3c = x_p.clone() * x_q.clone() * y_q_plus_y_p.clone() * nonexceptional_x_r;
            // x_p⋅x_q⋅(y_q + y_p)⋅(λ ⋅(x_p - x_r) - y_p - y_r) = 0
            let poly3d = x_p.clone() * x_q.clone() * y_q_plus_y_p * nonexceptional_y_r;

            // (1 - x_p * β) * (x_r - x_q) = 0
            let poly4a = (one.clone() - if_beta.clone()) * (x_r.clone() - x_q);
            // (1 - x_p * β) * (y_r - y_q) = 0
            let poly4b = (one.clone() - if_beta) * (y_r.clone() - y_q);
            // (1 - x_q * γ) * (x_r - x_p) = 0
            let poly5a = (one.clone() - if_gamma.clone()) * (x_r.clone() - x_p);
            // (1 - x_q * γ) * (y_r - y_p) = 0
            let poly5b = (one.clone() - if_gamma) * (y_r.clone() - y_p);
            // ((1 - (x_q - x_p) * α - (y_q + y_p) * δ)) * x_r
            let poly6a = (one.clone() - if_alpha.clone() - if_delta.clone()) * x_r;
            // ((1 - (x_q - x_p) * α - (y_q + y_p) * δ)) * y_r
            let poly6b = (one.clone() - if_alpha - if_delta) * y_r;

            Constraints::with_selector(
                q_add,
                [
                    ("1", poly1),
                    ("2", poly2),
                    ("3a", poly3a),
                    ("3b", poly3b),
                    ("3c", poly3c),
                    ("3d", poly3d),
                    ("4a", poly4a),
                    ("4b", poly4b),
                    ("5a", poly5a),
                    ("5b", poly5b),
                    ("6a", poly6a),
                    ("6b", poly6b),
                ],
            )
        });

        // | window | x_p   | y_p   |
        // | u      | acc_x | acc_y |
        //
        // https://p.z.cash/halo2-0.1:ecc-fixed-mul-coordinates
        // https://p.z.cash/halo2-0.1:ecc-fixed-mul-full-word
        //
        // The selector is the fixed column that holds `z + 1`. It is not zero on a
        // window row, and it is zero on all other rows.
        meta.create_gate("fixed-base window", |meta| {
            let q_fixed_window = meta.query_fixed(self.fixed_z_plus_one);
            let window = self.adv(meta, 0, 0);
            let x_p = self.adv(meta, 1, 0);
            let y_p = self.adv(meta, 2, 0);
            let u = self.adv(meta, 0, 1);
            let z = q_fixed_window.clone() - one.clone();

            let mut window_pow = one.clone();
            let mut interpolated_x = Expression::Constant(pallas::Base::ZERO);
            for coeff in self.lagrange.iter() {
                interpolated_x = interpolated_x + window_pow.clone() * meta.query_fixed(*coeff);
                window_pow = window_pow * window.clone();
            }

            // Check interpolation of x-coordinate
            let x_check = interpolated_x - x_p.clone();
            // Check that `y + z = u^2`, where `z` is fixed and `u`, `y` are witnessed
            let y_check = u.square() - y_p.clone() - z;
            // Check that (x, y) is on the curve
            let on_curve = y_p.square() - x_p.clone().square() * x_p - curve_b.clone();

            Constraints::with_selector(
                q_fixed_window,
                [
                    ("check x", x_check),
                    ("check y", y_check),
                    ("on-curve", on_curve),
                    ("window range check", range_check(window, H)),
                ],
            )
        });

        // The window point is P, the accumulator is Q, and the accumulator of the
        // next window is R.
        //
        // |        | x_p | y_p |
        // |        | x_q | y_q |
        // |        |     |     |
        // |        | x_r | y_r |
        //
        // https://p.z.cash/halo2-0.1:ecc-incomplete-addition
        meta.create_gate("fixed-base incomplete addition", |meta| {
            let q_fixed_add = meta.query_selector(self.q_fixed_add);
            let x_p = self.adv(meta, 1, 0);
            let y_p = self.adv(meta, 2, 0);
            let x_q = self.adv(meta, 1, 1);
            let y_q = self.adv(meta, 2, 1);
            let x_r = self.adv(meta, 1, next_step + 1);
            let y_r = self.adv(meta, 2, next_step + 1);

            // (x_r + x_q + x_p)⋅(x_p − x_q)^2 − (y_p − y_q)^2 = 0
            let poly1 = (x_r.clone() + x_q.clone() + x_p.clone())
                * (x_p.clone() - x_q.clone())
                * (x_p.clone() - x_q.clone())
                - (y_p.clone() - y_q.clone()).square();
            // (y_r + y_q)(x_p − x_q) − (y_p − y_q)(x_q − x_r) = 0
            let poly2 = (y_r + y_q.clone()) * (x_p - x_q.clone()) - (y_p - y_q) * (x_q - x_r);

            Constraints::with_selector(q_fixed_add, [("x_r", poly1), ("y_r", poly2)])
        });

        // One step of the incomplete chain. The gate is enabled on the first row of
        // a step, and also reads the step after. A step holds the running sum before
        // its bit; the running sum after its bit is in the step after.
        //
        // |   0 | x_a    | lambda_1 | lambda_2 |
        // |   1 | z_prev | x_p      | y_p      |
        // |   2 | x_a'   | lambda_1'| lambda_2'|
        // |   3 | z      | x_p'     | y_p'     |
        let y_a = |meta: &mut VirtualCells<'_, pallas::Base>, row: i32| {
            self.big_y_a(meta, row) * pallas::Base::TWO_INV
        };
        // https://p.z.cash/halo2-0.1:ecc-var-mul-incomplete-main-loop?partial
        // https://p.z.cash/halo2-0.1:ecc-var-mul-incomplete-last-row?partial
        let for_loop = |meta: &mut VirtualCells<'_, pallas::Base>,
                        y_a_next: Expression<pallas::Base>| {
            let one = Expression::Constant(pallas::Base::ONE);
            let z_cur = self.adv(meta, 0, next_step + 1);
            let z_prev = self.adv(meta, 0, 1);
            let x_a_cur = self.adv(meta, 0, 0);
            let x_a_next = self.adv(meta, 0, next_step);
            let x_p_cur = self.adv(meta, 1, 1);
            let y_p_cur = self.adv(meta, 2, 1);
            let lambda1_cur = self.adv(meta, 1, 0);
            let lambda2_cur = self.adv(meta, 2, 0);
            let y_a_cur = y_a(meta, 0);

            // The current bit in the scalar decomposition, k_i = z_i - 2⋅z_{i+1}.
            let k = z_cur - z_prev * pallas::Base::from(2);
            // Check booleanity of decomposition.
            let bool_check = bool_check(k.clone());
            // λ_{1,i}⋅(x_{A,i} − x_{P,i}) − y_{A,i} + (2k_i - 1) y_{P,i} = 0
            let gradient_1 = lambda1_cur * (x_a_cur.clone() - x_p_cur) - y_a_cur.clone()
                + (k * pallas::Base::from(2) - one) * y_p_cur;
            // λ_{2,i}^2 − x_{A,i-1} − x_{R,i} − x_{A,i} = 0
            let secant_line = lambda2_cur.clone().square()
                - x_a_next.clone()
                - self.x_r(meta, 0)
                - x_a_cur.clone();
            // λ_{2,i}⋅(x_{A,i} − x_{A,i-1}) − y_{A,i} − y_{A,i-1} = 0
            let gradient_2 = lambda2_cur * (x_a_cur - x_a_next) - y_a_cur - y_a_next;

            [
                ("bool_check", bool_check),
                ("gradient_1", gradient_1),
                ("secant_line", secant_line),
                ("gradient_2", gradient_2),
            ]
        };

        // The initial row holds the initial `y_a` in column 1. The running sum
        // before the first bit, in the first step, is zero.
        //
        // https://p.z.cash/halo2-0.1:ecc-var-mul-incomplete-first-row
        meta.create_gate("q_mul_1 == 1 checks", |meta| {
            let q_mul_1 = meta.query_selector(self.q_mul_1);
            let y_a_next = y_a(meta, next_step);
            let y_a_witnessed = self.adv(meta, 1, 0);
            let z_init = self.adv(meta, 0, next_step + 1);
            Constraints::with_selector(
                q_mul_1,
                [("init y_a", y_a_witnessed - y_a_next), ("init z", z_init)],
            )
        });

        // https://p.z.cash/halo2-0.1:ecc-var-mul-incomplete-main-loop?partial
        meta.create_gate("q_mul_2 == 1 checks", |meta| {
            let q_mul_2 = meta.query_selector(self.q_mul_2);
            let y_a_next = y_a(meta, next_step);
            // The base used in double-and-add remains constant.
            let x_p_check = self.adv(meta, 1, 1) - self.adv(meta, 1, next_step + 1);
            let y_p_check = self.adv(meta, 2, 1) - self.adv(meta, 2, next_step + 1);
            Constraints::with_selector(
                q_mul_2,
                [("x_p_check", x_p_check), ("y_p_check", y_p_check)]
                    .into_iter()
                    .chain(for_loop(meta, y_a_next)),
            )
        });

        // The rows after the last step hold the final `x_a` and `y_a`, and the
        // running sum after the last bit.
        //
        // https://p.z.cash/halo2-0.1:ecc-var-mul-incomplete-last-row?partial
        meta.create_gate("q_mul_3 == 1 checks", |meta| {
            let q_mul_3 = meta.query_selector(self.q_mul_3);
            let y_a_final = self.adv(meta, 1, next_step);
            Constraints::with_selector(q_mul_3, for_loop(meta, y_a_final))
        });

        // | z_{i+1} | base_y | y_p |
        // | z_i     |        |     |
        //
        // https://p.z.cash/halo2-0.1:ecc-var-mul-complete-gate
        meta.create_gate(
            "Decompose scalar for complete bits of variable-base mul",
            |meta| {
                let q_mul_complete = meta.query_selector(self.q_mul_complete);
                let z_prev = self.adv(meta, 0, 0);
                let base_y = self.adv(meta, 1, 0);
                let y_p = self.adv(meta, 2, 0);
                let z_next = self.adv(meta, 0, 1);

                // k_{i} = z_{i} - 2⋅z_{i+1}
                let k = z_next - Expression::Constant(pallas::Base::from(2)) * z_prev;
                let bool_check = bool_check(k.clone());
                // k_i = 0 => y_p = -base_y
                // k_i = 1 => y_p = base_y
                let y_switch = ternary(k, base_y.clone() - y_p.clone(), base_y + y_p);

                Constraints::with_selector(
                    q_mul_complete,
                    [("bool_check", bool_check), ("y_switch", y_switch)],
                )
            },
        );

        // | z_1 | x      | y      |
        // | z_0 | base_x | base_y |
        //
        // https://p.z.cash/halo2-0.1:ecc-var-mul-lsb-gate?partial
        meta.create_gate("LSB check", |meta| {
            let q_mul_lsb = meta.query_selector(self.q_mul_lsb);
            let z_1 = self.adv(meta, 0, 0);
            let x_p = self.adv(meta, 1, 0);
            let y_p = self.adv(meta, 2, 0);
            let z_0 = self.adv(meta, 0, 1);
            let base_x = self.adv(meta, 1, 1);
            let base_y = self.adv(meta, 2, 1);

            //    z_0 = 2 * z_1 + k_0
            // => k_0 = z_0 - 2 * z_1
            let lsb = z_0 - z_1 * pallas::Base::from(2);
            let bool_check = bool_check(lsb.clone());
            // `lsb` = 0 => (x_p, y_p) = (x, -y)
            // `lsb` = 1 => (x_p, y_p) = (0,0)
            let lsb_x = ternary(lsb.clone(), x_p.clone(), x_p - base_x);
            let lsb_y = ternary(lsb, y_p.clone(), y_p + base_y);

            Constraints::with_selector(
                q_mul_lsb,
                [
                    ("bool_check", bool_check),
                    ("lsb_x", lsb_x),
                    ("lsb_y", lsb_y),
                ],
            )
        });

        // | z_0   | k_254 | s              |
        // | z_130 | alpha | s_minus_lo_130 |
        // | eta   |       |                |
        //
        // https://p.z.cash/halo2-0.1:ecc-var-mul-overflow
        meta.create_gate("overflow checks", |meta| {
            let q_mul_overflow = meta.query_selector(self.q_mul_overflow);
            let one = Expression::Constant(pallas::Base::ONE);
            let two_pow_124 = Expression::Constant(pallas::Base::from_u128(1 << 124));
            let two_pow_130 =
                two_pow_124.clone() * Expression::Constant(pallas::Base::from_u128(1 << 6));

            let z_0 = self.adv(meta, 0, 0);
            let k_254 = self.adv(meta, 1, 0);
            let s = self.adv(meta, 2, 0);
            let z_130 = self.adv(meta, 0, 1);
            let alpha = self.adv(meta, 1, 1);
            // s_minus_lo_130 = s - sum_{i = 0}^{129} 2^i ⋅ s_i
            let s_minus_lo_130 = self.adv(meta, 2, 1);
            let eta = self.adv(meta, 0, 2);

            let s_check = s - (alpha.clone() + k_254.clone() * two_pow_130);
            // q = 2^254 + t_q is the Pallas scalar field modulus.
            let t_q = Expression::Constant(pallas::Base::from_u128(T_Q));
            // z_0 - alpha - t_q = 0 (mod p)
            let recovery = z_0 - alpha - t_q;
            // k_254 * (z_130 - 2^124) = 0
            let lo_zero = k_254.clone() * (z_130.clone() - two_pow_124);
            // k_254 * s_minus_lo_130 = 0
            let s_minus_lo_130_check = k_254.clone() * s_minus_lo_130.clone();
            // (1 - k_254) * (1 - z_130 * eta) * s_minus_lo_130 = 0
            let canonicity = (one.clone() - k_254) * (one - z_130 * eta) * s_minus_lo_130;

            Constraints::with_selector(
                q_mul_overflow,
                [
                    ("s_check", s_check),
                    ("recovery", recovery),
                    ("lo_zero", lo_zero),
                    ("s_minus_lo_130_check", s_minus_lo_130_check),
                    ("canonicity", canonicity),
                ],
            )
        });
    }

    /// Witnesses a non-identity point.
    pub(in crate::circuit::halo2::address_signature) fn witness_point(
        &self,
        mut layouter: impl Layouter<pallas::Base>,
        value: Value<pallas::Affine>,
    ) -> Result<Point, Error> {
        let coordinates = value.map(|point| point.coordinates().map(|c| (*c.x(), *c.y())));
        coordinates.error_if_known_and(|c| bool::from(c.is_none()))?;
        let coordinates = coordinates.map(|c| c.unwrap());
        layouter.assign_region(
            || "witness point",
            |mut region| {
                super::enter("witness point");
                self.q_point.enable(&mut region, 0)?;
                Ok(Point {
                    x: assign(&mut region, self.a[0], 0, coordinates.map(|c| c.0))?,
                    y: assign(&mut region, self.a[1], 0, coordinates.map(|c| c.1))?,
                })
            },
        )
    }

    /// Constrains `point` to be a non-identity point on the curve, and returns the
    /// constrained cells.
    pub(in crate::circuit::halo2::address_signature) fn check_point(
        &self,
        mut layouter: impl Layouter<pallas::Base>,
        point: &Point,
    ) -> Result<Point, Error> {
        layouter.assign_region(
            || "check point",
            |mut region| {
                super::enter("check point");
                self.q_point.enable(&mut region, 0)?;
                Ok(Point {
                    x: copy(&mut region, &point.x, self.a[0], 0)?,
                    y: copy(&mut region, &point.y, self.a[1], 0)?,
                })
            },
        )
    }

    /// Complete addition `p + q`.
    pub(in crate::circuit::halo2::address_signature) fn add(
        &self,
        mut layouter: impl Layouter<pallas::Base>,
        p: &Point,
        q: &Point,
    ) -> Result<Point, Error> {
        let witness = p.value().zip(q.value()).map(|(p, q)| AddWitness::new(p, q));
        let witness = witness.as_ref();
        layouter.assign_region(
            || "complete addition",
            |mut region| {
                super::enter("complete addition");
                self.q_add.enable(&mut region, 0)?;
                copy(&mut region, &p.x, self.a[0], 0)?;
                copy(&mut region, &p.y, self.a[1], 0)?;
                assign(&mut region, self.a[2], 0, witness.map(|w| w.lambda))?;
                copy(&mut region, &q.x, self.a[0], 1)?;
                copy(&mut region, &q.y, self.a[1], 1)?;
                assign(&mut region, self.a[2], 1, witness.map(|w| w.alpha))?;
                let x = assign(&mut region, self.a[0], 2, witness.map(|w| w.x_r))?;
                let y = assign(&mut region, self.a[1], 2, witness.map(|w| w.y_r))?;
                assign(&mut region, self.a[2], 2, witness.map(|w| w.beta))?;
                assign(&mut region, self.a[0], 3, witness.map(|w| w.gamma))?;
                assign(&mut region, self.a[1], 3, witness.map(|w| w.delta))?;
                Ok(Point { x, y })
            },
        )
    }

    /// Fixed-base scalar multiplication `[scalar] base` with a full-width scalar.
    ///
    /// The scalar is witnessed as 3-bit windows. It can be non-canonical.
    pub(in crate::circuit::halo2::address_signature) fn mul_fixed(
        &self,
        mut layouter: impl Layouter<pallas::Base>,
        base: &OrchardFixedBasesFull,
        scalar: Value<pallas::Scalar>,
    ) -> Result<Point, Error> {
        let lagrange_coeffs = base.lagrange_coeffs();
        let zs = base.z();
        assert_eq!(lagrange_coeffs.len(), NUM_WINDOWS);
        assert_eq!(zs.len(), NUM_WINDOWS);

        let witness = scalar.map(|scalar| FixedWitness::new(base, &scalar));
        let witness = witness.as_ref();

        // The last window point, and the accumulator before it is added.
        let (last, accumulator) = layouter.assign_region(
            || "fixed-base mul (incomplete addition)",
            |mut region| {
                super::enter("fixed-base mul (incomplete addition)");
                let mut first = None;
                let mut last = None;
                for window in 0..NUM_WINDOWS {
                    let row = window * STEP_ROWS;
                    // https://p.z.cash/halo2-0.1:ecc-fixed-mul-load-base
                    for (column, coeff) in self.lagrange.iter().zip(lagrange_coeffs[window]) {
                        region.assign_fixed(
                            || "Lagrange coefficient",
                            *column,
                            row,
                            || Value::known(coeff),
                        )?;
                    }
                    // `z + 1` is not zero: `z` is a small integer.
                    region.assign_fixed(
                        || "z + 1",
                        self.fixed_z_plus_one,
                        row,
                        || Value::known(pallas::Base::from(zs[window]) + pallas::Base::ONE),
                    )?;

                    assign(
                        &mut region,
                        self.a[0],
                        row,
                        witness.map(|w| w.windows[window]),
                    )?;
                    let point = Point {
                        x: assign(
                            &mut region,
                            self.a[1],
                            row,
                            witness.map(|w| w.points[window].0),
                        )?,
                        y: assign(
                            &mut region,
                            self.a[2],
                            row,
                            witness.map(|w| w.points[window].1),
                        )?,
                    };
                    assign(
                        &mut region,
                        self.a[0],
                        row + 1,
                        witness.map(|w| w.us[window]),
                    )?;

                    // The accumulator before this window point is added. Before the
                    // second window, it is the first window point.
                    let accumulator = match (window, &first) {
                        (0, _) => None,
                        (1, Some(Point { x, y })) => Some(Point {
                            x: copy(&mut region, x, self.a[1], row + 1)?,
                            y: copy(&mut region, y, self.a[2], row + 1)?,
                        }),
                        _ => Some(Point {
                            x: assign(
                                &mut region,
                                self.a[1],
                                row + 1,
                                witness.map(|w| w.accumulators[window].0),
                            )?,
                            y: assign(
                                &mut region,
                                self.a[2],
                                row + 1,
                                witness.map(|w| w.accumulators[window].1),
                            )?,
                        }),
                    };

                    // All windows but the first and the last add their point to the
                    // accumulator with incomplete addition.
                    if window > 0 && window + 1 < NUM_WINDOWS {
                        self.q_fixed_add.enable(&mut region, row)?;
                    }
                    if window == 0 {
                        first = Some(point.clone());
                    }
                    last = accumulator.map(|accumulator| (point, accumulator));
                }
                Ok(last.expect("there is more than one window"))
            },
        )?;

        // The last window uses complete addition.
        self.add(
            layouter.namespace(|| "fixed-base mul (last window)"),
            &last,
            &accumulator,
        )
    }

    /// Variable-base scalar multiplication `[scalar] base`.
    ///
    /// `scalar` is a base field element. Its decomposition is constrained to be
    /// canonical. `base` must be a non-identity point; each step of the incomplete
    /// chain is constrained to use the cells of `base`.
    pub(in crate::circuit::halo2::address_signature) fn mul(
        &self,
        mut layouter: impl Layouter<pallas::Base>,
        scalar: &Cell,
        base: &Point,
    ) -> Result<Point, Error> {
        // Big-endian bits of `k = scalar + t_q`.
        let bits = scalar.value().map(|scalar| {
            let mut bits = scalar_mul_bits(scalar);
            bits.reverse();
            bits
        });
        let bit = |index: usize| bits.as_ref().map(|bits| bits[index]);
        let (base_x, base_y) = base.value().unzip();

        // Initialize the accumulator `acc = [2]base` using complete addition.
        let acc = self.add(layouter.namespace(|| "[2] base"), base, base)?;

        // The base of the chain is the real base. A test can replace it, to build
        // the witness of a prover that tries to use its own base.
        let chain_base = super::fault::chain_base(base.value());
        let (chain_x, chain_y) = chain_base.unzip();
        let witness = chain_base
            .zip(acc.value())
            .zip(bits.as_ref())
            .map(|((base, acc), bits)| IncompleteWitness::new(base, acc, &bits[..INCOMPLETE_BITS]));
        witness.error_if_known_and(|witness| witness.is_none())?;
        let witness = witness.map(|witness| witness.expect("checked above"));
        let witness = witness.as_ref();

        let (mut acc, z_254, z_130, mut z) = layouter.assign_region(
            || "variable-base mul (incomplete addition)",
            |mut region| {
                super::enter("variable-base mul (incomplete addition)");
                // Initial row.
                self.q_mul_1.enable(&mut region, 0)?;
                copy(&mut region, &acc.y, self.a[1], 0)?;

                // The running sum after bit `index` is in the second row of the step
                // after it.
                let mut z_254 = None;
                let mut z_130 = None;
                for index in 0..INCOMPLETE_BITS {
                    let row = (index + 1) * STEP_ROWS;
                    if index + 1 < INCOMPLETE_BITS {
                        self.q_mul_2.enable(&mut region, row)?;
                    } else {
                        self.q_mul_3.enable(&mut region, row)?;
                    }

                    if index == 0 {
                        // The initial `x_a`, and the anchor of the base.
                        copy(&mut region, &acc.x, self.a[0], row)?;
                        copy_with_value(&mut region, &base.x, self.a[1], row + 1, chain_x)?;
                        copy_with_value(&mut region, &base.y, self.a[2], row + 1, chain_y)?;
                    } else {
                        assign(&mut region, self.a[0], row, witness.map(|w| w.x_a[index]))?;
                        assign(&mut region, self.a[1], row + 1, chain_x)?;
                        assign(&mut region, self.a[2], row + 1, chain_y)?;
                    }
                    assign(
                        &mut region,
                        self.a[1],
                        row,
                        witness.map(|w| w.lambda_1[index]),
                    )?;
                    assign(
                        &mut region,
                        self.a[2],
                        row,
                        witness.map(|w| w.lambda_2[index]),
                    )?;
                    let z_before = assign(
                        &mut region,
                        self.a[0],
                        row + 1,
                        match index {
                            0 => Value::known(pallas::Base::ZERO),
                            _ => witness.map(|w| w.z[index - 1]),
                        },
                    )?;
                    if index == 1 {
                        z_254 = Some(z_before.clone());
                    }
                    if index == BITS_TO_Z_130 {
                        z_130 = Some(z_before);
                    }
                }

                // The final accumulator.
                let row = (INCOMPLETE_BITS + 1) * STEP_ROWS;
                let acc = Point {
                    x: assign(
                        &mut region,
                        self.a[0],
                        row,
                        witness.map(|w| w.x_a[INCOMPLETE_BITS]),
                    )?,
                    y: assign(&mut region, self.a[1], row, witness.map(|w| w.y_final))?,
                };
                let z_last = assign(
                    &mut region,
                    self.a[0],
                    row + 1,
                    witness.map(|w| w.z[INCOMPLETE_BITS - 1]),
                )?;
                Ok((
                    acc,
                    z_254.expect("the chain has more than one bit"),
                    z_130.expect("the chain passes bit 130"),
                    z_last,
                ))
            },
        )?;

        // Bits k_3 to k_1 use complete addition: acc = (acc + U) + acc, where U is
        // the base if the bit is set, and its negation if not.
        for index in INCOMPLETE_BITS..INCOMPLETE_BITS + COMPLETE_BITS {
            let k = bit(index);
            let (u_y, z_next) = layouter.assign_region(
                || "variable-base mul (complete bit)",
                |mut region| {
                    super::enter("variable-base mul (complete bit)");
                    self.q_mul_complete.enable(&mut region, 0)?;
                    let z_prev = copy(&mut region, &z, self.a[0], 0)?;
                    copy(&mut region, &base.y, self.a[1], 0)?;
                    let u_y = assign(
                        &mut region,
                        self.a[2],
                        0,
                        base_y.zip(k).map(|(y, k)| if k { y } else { -y }),
                    )?;
                    let z_next = assign(
                        &mut region,
                        self.a[0],
                        1,
                        z_prev
                            .value()
                            .zip(k)
                            .map(|(z, k)| z.double() + pallas::Base::from(u64::from(k))),
                    )?;
                    Ok((u_y, z_next))
                },
            )?;
            z = z_next;
            let u = Point {
                x: base.x.clone(),
                y: u_y,
            };
            let tmp = self.add(layouter.namespace(|| "acc + U"), &u, &acc)?;
            acc = self.add(layouter.namespace(|| "acc + U + acc"), &acc, &tmp)?;
        }

        // The least significant bit: add `-base` if it is 0, and the identity if it
        // is 1.
        let lsb = bit(SCALAR_BITS - 1);
        let (p, z_0) = layouter.assign_region(
            || "variable-base mul (least significant bit)",
            |mut region| {
                super::enter("variable-base mul (least significant bit)");
                self.q_mul_lsb.enable(&mut region, 0)?;
                let z_1 = copy(&mut region, &z, self.a[0], 0)?;
                let zero = pallas::Base::ZERO;
                let p = Point {
                    x: assign(
                        &mut region,
                        self.a[1],
                        0,
                        base_x.zip(lsb).map(|(x, lsb)| if lsb { zero } else { x }),
                    )?,
                    y: assign(
                        &mut region,
                        self.a[2],
                        0,
                        base_y.zip(lsb).map(|(y, lsb)| if lsb { zero } else { -y }),
                    )?,
                };
                let z_0 = assign(
                    &mut region,
                    self.a[0],
                    1,
                    z_1.value()
                        .zip(lsb)
                        .map(|(z, lsb)| z.double() + pallas::Base::from(u64::from(lsb))),
                )?;
                copy(&mut region, &base.x, self.a[1], 1)?;
                copy(&mut region, &base.y, self.a[2], 1)?;
                Ok((p, z_0))
            },
        )?;
        let result = self.add(layouter.namespace(|| "acc + P"), &p, &acc)?;
        super::fault::record_mul_result(result.value());

        // Overflow check: `z_0 = scalar + t_q`, and the decomposition is canonical.
        //
        // s = scalar + k_254 ⋅ 2^130. Its low 130 bits are removed with thirteen
        // 10-bit lookups.
        let two_pow_130 = pallas::Base::from_u128(1 << 65).square();
        let s = scalar
            .value()
            .zip(z_254.value())
            .map(|(scalar, k_254)| *scalar + *k_254 * two_pow_130);
        let s_sums = self.range_check(
            layouter.namespace(|| "decompose s_{0..=129}"),
            s,
            OVERFLOW_WORDS,
        )?;
        layouter.assign_region(
            || "variable-base mul (overflow check)",
            |mut region| {
                super::enter("variable-base mul (overflow check)");
                self.q_mul_overflow.enable(&mut region, 0)?;
                copy(&mut region, &z_0, self.a[0], 0)?;
                copy(&mut region, &z_254, self.a[1], 0)?;
                copy(&mut region, &s_sums[0], self.a[2], 0)?;
                let z_130 = copy(&mut region, &z_130, self.a[0], 1)?;
                copy(&mut region, scalar, self.a[1], 1)?;
                copy(&mut region, &s_sums[OVERFLOW_WORDS], self.a[2], 1)?;
                // η = inv0(z_130)
                assign(
                    &mut region,
                    self.a[0],
                    2,
                    z_130.value().map(|z_130| inv0(*z_130)),
                )?;
                Ok(())
            },
        )?;

        Ok(result)
    }
}
