import AddressSignature.Imports

/-!
# The constraint system of the narrow address signature circuit

This file is the Lean model of the constraint system that
`crates/orchard/src/circuit/halo2/address_signature/chip.rs` and its submodules
`chip/ecc.rs`, `chip/sinsemilla.rs`, `chip/commit_ivk.rs` create:

* 3 advice columns, 1 instance column;
* 8 Lagrange columns, the `z + 1` column, the ternary lookup selector column;
* 13 binary selectors (before Halo 2 packs them into fixed columns);
* 15 gates with 60 polynomial constraints;
* 1 lookup argument with 3 input expressions into the Sinsemilla generator table.

Each polynomial below has the shape of the Rust expression that creates it. A cell
`(column, row)` of the Rust code is `w.a column (r + row)` here, where `r` is the row
on which the selector is read.
-/

namespace AddressSignature

open Zcash.Circuits

/-- The Pallas base field. All cells hold elements of this field. -/
abbrev Fp := Zcash.Circuits.Fp

/-- The values of all columns of the circuit, by row. -/
structure Assignment where
  /-- Advice column `a0`. -/
  a0 : ℕ → Fp
  /-- Advice column `a1`. -/
  a1 : ℕ → Fp
  /-- Advice column `a2`. -/
  a2 : ℕ → Fp
  /-- The instance column `primary`. -/
  inst : ℕ → Fp
  /-- The fixed columns `lagrange[0..8]`. -/
  lagrange : Fin 8 → ℕ → Fp
  /-- The fixed column `fixed_z_plus_one`. -/
  fixedZPlusOne : ℕ → Fp
  /-- The fixed column `f_lookup`. -/
  fLookup : ℕ → Fp
  qPoint : ℕ → Fp
  qAdd : ℕ → Fp
  qFixedAdd : ℕ → Fp
  qMul1 : ℕ → Fp
  qMul2 : ℕ → Fp
  qMul3 : ℕ → Fp
  qMulComplete : ℕ → Fp
  qMulLsb : ℕ → Fp
  qMulOverflow : ℕ → Fp
  qSinInit : ℕ → Fp
  qShift : ℕ → Fp
  qCommitIvkAk : ℕ → Fp
  qCommitIvkNk : ℕ → Fp

namespace Assignment

variable (w : Assignment)

/-! ## Shared expressions -/

/-- `pallas::Base::TWO_INV`. -/
def twoInv : Fp := (2 : Fp)⁻¹

/-- `halo2_gadgets::utilities::bool_check`. -/
def boolCheck (v : Fp) : Fp := v * (1 - v)

/-- `halo2_gadgets::utilities::ternary`. -/
def ternary (a b c : Fp) : Fp := a * b + (1 - a) * c

/-- `halo2_gadgets::utilities::range_check(word, 8)`. -/
def rangeCheck8 (v : Fp) : Fp :=
  v * (1 - v) * (2 - v) * (3 - v) * (4 - v) * (5 - v) * (6 - v) * (7 - v)

/-- `Config::x_r`: `x_r = lambda_1^2 - x_a - x_p` of the step that starts at row `r`. -/
def xR (r : ℕ) : Fp := w.a1 r * w.a1 r - w.a0 r - w.a1 (r + 1)

/-- `Config::big_y_a`: `Y_A = (lambda_1 + lambda_2) * (x_a - x_r)`. -/
def bigYA (r : ℕ) : Fp := (w.a1 r + w.a2 r) * (w.a0 r - w.xR r)

/-- `y_a = Y_A / 2` of the step that starts at row `r`. -/
def yA (r : ℕ) : Fp := w.bigYA r * twoInv

/-! ## Gates of `chip/ecc.rs` -/

/-- Gate "witness non-identity point" (selector `q_point`). -/
def pointPolys (r : ℕ) : List Fp :=
  [w.a1 r * w.a1 r - w.a0 r * w.a0 r * w.a0 r - pallasB]

/-- Gate "complete addition" (selector `q_add`). -/
def addPolys (r : ℕ) : List Fp :=
  let x_p := w.a0 r
  let y_p := w.a1 r
  let lambda := w.a2 r
  let x_q := w.a0 (r + 1)
  let y_q := w.a1 (r + 1)
  let alpha := w.a2 (r + 1)
  let x_r := w.a0 (r + 2)
  let y_r := w.a1 (r + 2)
  let beta := w.a2 (r + 2)
  let gamma := w.a0 (r + 3)
  let delta := w.a1 (r + 3)
  let if_alpha := (x_q - x_p) * alpha
  let if_beta := x_p * beta
  let if_gamma := x_q * gamma
  let if_delta := (y_q + y_p) * delta
  let nonexceptional_x_r := lambda * lambda - x_p - x_q - x_r
  let nonexceptional_y_r := lambda * (x_p - x_r) - y_p - y_r
  [ (x_q - x_p) * ((x_q - x_p) * lambda - (y_q - y_p)),
    (1 - if_alpha) * (2 * y_p * lambda - 3 * (x_p * x_p)),
    x_p * x_q * (x_q - x_p) * nonexceptional_x_r,
    x_p * x_q * (x_q - x_p) * nonexceptional_y_r,
    x_p * x_q * (y_q + y_p) * nonexceptional_x_r,
    x_p * x_q * (y_q + y_p) * nonexceptional_y_r,
    (1 - if_beta) * (x_r - x_q),
    (1 - if_beta) * (y_r - y_q),
    (1 - if_gamma) * (x_r - x_p),
    (1 - if_gamma) * (y_r - y_p),
    (1 - if_alpha - if_delta) * x_r,
    (1 - if_alpha - if_delta) * y_r ]

/-- The interpolation polynomial of the fixed-base window gate, read from the eight
Lagrange columns on row `r`. -/
def interpolatedX (r : ℕ) : Fp :=
  let k := w.a0 r
  w.lagrange 0 r +
    k * w.lagrange 1 r +
    k * k * w.lagrange 2 r +
    k * k * k * w.lagrange 3 r +
    k * k * k * k * w.lagrange 4 r +
    k * k * k * k * k * w.lagrange 5 r +
    k * k * k * k * k * k * w.lagrange 6 r +
    k * k * k * k * k * k * k * w.lagrange 7 r

/-- Gate "fixed-base window". Its selector is the fixed column `fixed_z_plus_one`,
and the gate uses `z = fixed_z_plus_one - 1` (shortcut 1 of section 6). -/
def fixedWindowPolys (r : ℕ) : List Fp :=
  let window := w.a0 r
  let x_p := w.a1 r
  let y_p := w.a2 r
  let u := w.a0 (r + 1)
  let z := w.fixedZPlusOne r - 1
  [ w.interpolatedX r - x_p,
    u * u - y_p - z,
    y_p * y_p - x_p * x_p * x_p - pallasB,
    rangeCheck8 window ]

/-- Gate "fixed-base incomplete addition" (selector `q_fixed_add`). -/
def fixedAddPolys (r : ℕ) : List Fp :=
  let x_p := w.a1 r
  let y_p := w.a2 r
  let x_q := w.a1 (r + 1)
  let y_q := w.a2 (r + 1)
  let x_r := w.a1 (r + 3)
  let y_r := w.a2 (r + 3)
  [ (x_r + x_q + x_p) * (x_p - x_q) * (x_p - x_q) - (y_p - y_q) * (y_p - y_q),
    (y_r + y_q) * (x_p - x_q) - (y_p - y_q) * (x_q - x_r) ]

/-- The four constraints `for_loop` of one step of the variable-base incomplete
chain. `yANext` is the `y`-coordinate of the accumulator after the step. -/
def mulLoopPolys (r : ℕ) (yANext : Fp) : List Fp :=
  let z_cur := w.a0 (r + 3)
  let z_prev := w.a0 (r + 1)
  let x_a_cur := w.a0 r
  let x_a_next := w.a0 (r + 2)
  let x_p_cur := w.a1 (r + 1)
  let y_p_cur := w.a2 (r + 1)
  let lambda1_cur := w.a1 r
  let lambda2_cur := w.a2 r
  let y_a_cur := w.yA r
  let k := z_cur - z_prev * 2
  [ boolCheck k,
    lambda1_cur * (x_a_cur - x_p_cur) - y_a_cur + (k * 2 - 1) * y_p_cur,
    lambda2_cur * lambda2_cur - x_a_next - w.xR r - x_a_cur,
    lambda2_cur * (x_a_cur - x_a_next) - y_a_cur - yANext ]

/-- Gate "q_mul_1 == 1 checks": the initial row of the variable-base chain. -/
def mul1Polys (r : ℕ) : List Fp :=
  [ w.a1 r - w.yA (r + 2), w.a0 (r + 3) ]

/-- Gate "q_mul_2 == 1 checks": the main loop of the variable-base chain. -/
def mul2Polys (r : ℕ) : List Fp :=
  [ w.a1 (r + 1) - w.a1 (r + 3), w.a2 (r + 1) - w.a2 (r + 3) ]
    ++ w.mulLoopPolys r (w.yA (r + 2))

/-- Gate "q_mul_3 == 1 checks": the last bit of the variable-base chain. -/
def mul3Polys (r : ℕ) : List Fp :=
  w.mulLoopPolys r (w.a1 (r + 2))

/-- Gate "Decompose scalar for complete bits of variable-base mul"
(selector `q_mul_complete`). -/
def mulCompletePolys (r : ℕ) : List Fp :=
  let z_prev := w.a0 r
  let base_y := w.a1 r
  let y_p := w.a2 r
  let z_next := w.a0 (r + 1)
  let k := z_next - 2 * z_prev
  [ boolCheck k, ternary k (base_y - y_p) (base_y + y_p) ]

/-- Gate "LSB check" (selector `q_mul_lsb`). -/
def mulLsbPolys (r : ℕ) : List Fp :=
  let z_1 := w.a0 r
  let x_p := w.a1 r
  let y_p := w.a2 r
  let z_0 := w.a0 (r + 1)
  let base_x := w.a1 (r + 1)
  let base_y := w.a2 (r + 1)
  let lsb := z_0 - z_1 * 2
  [ boolCheck lsb, ternary lsb x_p (x_p - base_x), ternary lsb y_p (y_p + base_y) ]

/-- Gate "overflow checks" (selector `q_mul_overflow`). -/
def mulOverflowPolys (r : ℕ) : List Fp :=
  let z_0 := w.a0 r
  let k_254 := w.a1 r
  let s := w.a2 r
  let z_130 := w.a0 (r + 1)
  let alpha := w.a1 (r + 1)
  let s_minus_lo_130 := w.a2 (r + 1)
  let eta := w.a0 (r + 2)
  [ s - (alpha + k_254 * (2 ^ 124 * 2 ^ 6)),
    z_0 - alpha - Ecc.tQ,
    k_254 * (z_130 - 2 ^ 124),
    k_254 * s_minus_lo_130,
    (1 - k_254) * (1 - z_130 * eta) * s_minus_lo_130 ]

/-! ## Gates and lookup of `chip/sinsemilla.rs` -/

/-- `f_sin = f_lookup * (2 - f_lookup)`: 1 on a Sinsemilla word (shortcut 2). -/
def fSin (r : ℕ) : Fp := w.fLookup r * (2 - w.fLookup r)

/-- `f_rc = f_lookup * (f_lookup - 1) / 2`: 1 on a range-check row (shortcut 2). -/
def fRc (r : ℕ) : Fp := w.fLookup r * (w.fLookup r - 1) * twoInv

/-- The running-sum mode `f_s2`, read from `lagrange[2]` (shortcut 3). -/
def fS2 (r : ℕ) : Fp := w.lagrange 2 r

/-- `q_s3 = f_s2 * (f_s2 - 1)`. -/
def qS3 (r : ℕ) : Fp := w.fS2 r * (w.fS2 r - 1)

/-- `q_run = f_s2 - q_s3`. -/
def qRun (r : ℕ) : Fp := w.fS2 r - w.qS3 r

/-- The `y`-coordinate of the generator of a Sinsemilla word:
`y_p = Y_A / 2 - lambda_1 * (x_a - x_p)`. -/
def sinYP (r : ℕ) : Fp := w.bigYA r * twoInv - w.a1 r * (w.a0 r - w.a1 (r + 1))

/-- The first input expression of the lookup: the table index. -/
def lookupIndex (r : ℕ) : Fp :=
  let sinsemilla_word := w.a0 (r + 1) - w.qRun r * w.a0 (r + 3) * 2 ^ 10
  let range_check_word := w.a0 r - w.qRun r * w.a0 (r + 1) * 2 ^ 10
  w.fSin r * sinsemilla_word + w.fRc r * range_check_word

/-- The second input expression of the lookup: the `x`-coordinate. `initX` is
`x(S_0)`. -/
def lookupX (initX : Fp) (r : ℕ) : Fp :=
  w.fSin r * w.a1 (r + 1) + w.fRc r * w.a1 r + (1 - w.fSin r - w.fRc r) * initX

/-- The third input expression of the lookup: the `y`-coordinate. `initY` is
`y(S_0)`. -/
def lookupY (initY : Fp) (r : ℕ) : Fp :=
  w.fSin r * w.sinYP r + w.fRc r * w.a2 r + (1 - w.fSin r - w.fRc r) * initY

/-- Gate "Initial Q" (selector `q_sin_init`). `x_Q` and `y_Q` are read from
`lagrange[0]` and `lagrange[1]` (shortcut 3). -/
def sinInitPolys (r : ℕ) : List Fp :=
  [ w.a0 r - w.lagrange 0 r, w.lagrange 1 r * 2 - w.bigYA r ]

/-- Gate "Sinsemilla gate". Its selector is `f_sin`. -/
def sinPolys (r : ℕ) : List Fp :=
  let lambda_1_next := w.a1 (r + 2)
  let lambda_2_cur := w.a2 r
  let x_a_cur := w.a0 r
  let x_a_next := w.a0 (r + 2)
  [ lambda_2_cur * lambda_2_cur - (x_a_next + w.xR r + x_a_cur),
    lambda_2_cur * 4 * (x_a_cur - x_a_next)
      - (w.bigYA r * 2 + (2 - w.qS3 r) * w.bigYA (r + 2) + w.qS3 r * 2 * lambda_1_next) ]

/-- Gate "Short lookup bitshift" (selector `q_shift`). The shift factor is read
from `lagrange[0]` (shortcut 3). -/
def shiftPolys (r : ℕ) : List Fp :=
  [ w.a0 r * w.lagrange 0 r - w.a0 (r + 1) ]

/-! ## Gates of `chip/commit_ivk.rs` -/

/-- Gate "CommitIvk canonicity check of ak" (selector `q_commit_ivk_ak`). -/
def commitIvkAkPolys (r : ℕ) : List Fp :=
  let ak := w.a0 r
  let a := w.a1 r
  let b_whole := w.a2 r
  let b_0 := w.a0 (r + 1)
  let b_1 := w.a1 (r + 1)
  let b_2 := w.a2 (r + 1)
  let z13_a := w.a0 (r + 2)
  let a_prime := w.a1 (r + 2)
  let z13_a_prime := w.a2 (r + 2)
  [ boolCheck b_1,
    b_whole - (b_0 + b_1 * 2 ^ 4 + b_2 * 2 ^ 5),
    a + b_0 * 2 ^ 250 + b_1 * 2 ^ 254 - ak,
    b_1 * b_0,
    b_1 * z13_a,
    a + 2 ^ 130 - tP - a_prime,
    b_1 * z13_a_prime ]

/-- Gate "CommitIvk canonicity check of nk" (selector `q_commit_ivk_nk`). -/
def commitIvkNkPolys (r : ℕ) : List Fp :=
  let nk := w.a0 r
  let c := w.a1 r
  let d_whole := w.a2 r
  let d_0 := w.a0 (r + 1)
  let d_1 := w.a1 (r + 1)
  let b_2 := w.a2 (r + 1)
  let z13_c := w.a0 (r + 2)
  let b2_c_prime := w.a1 (r + 2)
  let z14_b2_c_prime := w.a2 (r + 2)
  [ boolCheck d_1,
    d_whole - (d_0 + d_1 * 2 ^ 9),
    b_2 + c * 2 ^ 5 + d_0 * 2 ^ 245 + d_1 * 2 ^ 254 - nk,
    d_1 * d_0,
    d_1 * z13_c,
    b_2 + c * 2 ^ 5 + 2 ^ 140 - tP - b2_c_prime,
    d_1 * z14_b2_c_prime ]

/-! ## The constraint system -/

/-- The 15 gates: the selector expression and the constraint polynomials of each. -/
def gates : List ((ℕ → Fp) × (ℕ → List Fp)) :=
  [ (w.qPoint, w.pointPolys),
    (w.qAdd, w.addPolys),
    (w.fixedZPlusOne, w.fixedWindowPolys),
    (w.qFixedAdd, w.fixedAddPolys),
    (w.qMul1, w.mul1Polys),
    (w.qMul2, w.mul2Polys),
    (w.qMul3, w.mul3Polys),
    (w.qMulComplete, w.mulCompletePolys),
    (w.qMulLsb, w.mulLsbPolys),
    (w.qMulOverflow, w.mulOverflowPolys),
    (w.qSinInit, w.sinInitPolys),
    (w.fSin, w.sinPolys),
    (w.qShift, w.shiftPolys),
    (w.qCommitIvkAk, w.commitIvkAkPolys),
    (w.qCommitIvkNk, w.commitIvkNkPolys) ]

/-- A gate holds on the first `n` rows: on each row, the selector times each
constraint polynomial is zero. -/
def GateHolds (n : ℕ) (g : (ℕ → Fp) × (ℕ → List Fp)) : Prop :=
  ∀ r, r < n → ∀ p ∈ g.2 r, g.1 r * p = 0

/-- The lookup argument holds on the first `n` rows: on each row, the three input
expressions are a row `(i, x(S_i), y(S_i))` of the generator table, `i < 2^10`.

`S` is the Sinsemilla generator table. The table has exactly one row for each
10-bit index. -/
def LookupHolds (S : ℕ → Point Fp) (n : ℕ) : Prop :=
  ∀ r, r < n → ∃ i : ℕ, i < 2 ^ 10 ∧
    w.lookupIndex r = (i : Fp) ∧
    w.lookupX (S 0).x r = (S i).x ∧
    w.lookupY (S 0).y r = (S i).y

/-- All gate constraints and the lookup hold on the first `n` rows. `n` is the
number of usable rows. -/
structure Constrained (S : ℕ → Point Fp) (n : ℕ) : Prop where
  gates : ∀ g ∈ w.gates, GateHolds n g
  lookup : w.LookupHolds S n

end Assignment

end AddressSignature
