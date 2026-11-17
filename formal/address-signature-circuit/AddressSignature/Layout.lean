import AddressSignature.Spec
import AddressSignature.Gadgets.FixedMul
import AddressSignature.Gadgets.CommitIvk
import AddressSignature.Gadgets.MulFull

/-!
# The layout of the circuit: regions, fixed cells, copy constraints

`Circuit::synthesize` of `address_signature.rs` assigns 32 regions. This file
records, for each region, the row at which the floor planner places it
(`Placement`), and the facts that synthesis fixes (`Wired`):

* the fixed cells: selectors, `z + 1`, the Lagrange coefficients, `f_lookup`, and
  the data in the Lagrange columns (`x_Q`, `y_Q`, the shift factor, `f_s2`);
* the copy constraints between advice cells, and between advice cells and the
  instance column.

The soundness theorem holds for every placement. It does not use that regions are
disjoint, and it does not use that a fixed cell is zero outside the regions.
-/

namespace AddressSignature

open Zcash.Circuits

/-- The first row of each region, in synthesis order. -/
structure Placement where
  /-- "witness point" for `g_d` (1 row). -/
  gd : ℕ
  /-- "witness point" for `ak_P` (1 row). -/
  ak : ℕ
  /-- "fixed-base mul (incomplete addition)" for `[α] G^SpendAuth` (170 rows). -/
  alphaMul : ℕ
  /-- "complete addition" of the last window of `[α] G^SpendAuth` (4 rows). -/
  alphaAdd : ℕ
  /-- "complete addition" `rk = [α] G^SpendAuth + ak_P` (4 rows). -/
  rkAdd : ℕ
  /-- "short range check" of `b_0` (2 rows). -/
  b0 : ℕ
  /-- "short range check" of `b_2` (2 rows). -/
  b2 : ℕ
  /-- "short range check" of `d_0` (2 rows). -/
  d0 : ℕ
  /-- "Sinsemilla hash" of `ak ‖ nk` (104 rows). -/
  hash : ℕ
  /-- "fixed-base mul (incomplete addition)" for `[rivk] R` (170 rows). -/
  rivkMul : ℕ
  /-- "complete addition" of the last window of `[rivk] R` (4 rows). -/
  rivkAdd : ℕ
  /-- "complete addition" `Hash + [rivk] R` (4 rows). -/
  commitAdd : ℕ
  /-- "range check" of `a'` (14 rows). -/
  aPrime : ℕ
  /-- "range check" of `b2c'` (15 rows). -/
  b2cPrime : ℕ
  /-- "CommitIvk canonicity of ak" (3 rows). -/
  canonAk : ℕ
  /-- "CommitIvk canonicity of nk" (3 rows). -/
  canonNk : ℕ
  /-- "complete addition" `[2] g_d` (4 rows). -/
  dbl : ℕ
  /-- "variable-base mul (incomplete addition)" (506 rows). -/
  inc : ℕ
  /-- "variable-base mul (complete bit)" for `k_3` (2 rows), and its two complete
  additions (4 rows each). -/
  bit0 : ℕ
  addU0 : ℕ
  addAcc0 : ℕ
  /-- The same three regions for `k_2`. -/
  bit1 : ℕ
  addU1 : ℕ
  addAcc1 : ℕ
  /-- The same three regions for `k_1`. -/
  bit2 : ℕ
  addU2 : ℕ
  addAcc2 : ℕ
  /-- "variable-base mul (least significant bit)" (2 rows). -/
  lsb : ℕ
  /-- "complete addition" of the least significant bit (4 rows). -/
  lsbAdd : ℕ
  /-- "range check" of `s` (14 rows). -/
  sRange : ℕ
  /-- "variable-base mul (overflow check)" (3 rows). -/
  overflow : ℕ
  /-- "check point" for `pk_d` (1 row). -/
  pkd : ℕ

/-- The fixed cells and copy constraints that `Circuit::synthesize` creates, for
the placement `L`, with all regions in the first `n` rows. -/
structure Wired (w : Assignment) (L : Placement) (n : ℕ) : Prop where
  -- All regions are in the usable rows
  fitsGd : L.gd + 1 ≤ n
  fitsAk : L.ak + 1 ≤ n
  fitsAlphaMul : L.alphaMul + 170 ≤ n
  fitsAlphaAdd : L.alphaAdd + 4 ≤ n
  fitsRkAdd : L.rkAdd + 4 ≤ n
  fitsB0 : L.b0 + 2 ≤ n
  fitsB2 : L.b2 + 2 ≤ n
  fitsD0 : L.d0 + 2 ≤ n
  fitsHash : L.hash + 104 ≤ n
  fitsRivkMul : L.rivkMul + 170 ≤ n
  fitsRivkAdd : L.rivkAdd + 4 ≤ n
  fitsCommitAdd : L.commitAdd + 4 ≤ n
  fitsAPrime : L.aPrime + 14 ≤ n
  fitsB2cPrime : L.b2cPrime + 15 ≤ n
  fitsCanonAk : L.canonAk + 3 ≤ n
  fitsCanonNk : L.canonNk + 3 ≤ n
  fitsMul : Assignment.MulFits n L.dbl L.inc L.bit0 L.addU0 L.addAcc0 L.bit1 L.addU1 L.addAcc1
    L.bit2 L.addU2 L.addAcc2 L.lsb L.lsbAdd L.sRange L.overflow
  fitsPkd : L.pkd + 1 ≤ n
  -- `g_d` and `ak_P` (`witness_point`, `constrain_instance`)
  gdSel : w.qPoint L.gd = 1
  gdX : w.a0 L.gd = w.inst 0
  gdY : w.a1 L.gd = w.inst 1
  akSel : w.qPoint L.ak = 1
  -- Spend authority: `[α] G^SpendAuth` (`mul_fixed`) and `rk` (`add`)
  alphaMul : w.FixedMulRegion spendAuthG L.alphaMul
  alphaAddSel : w.qAdd L.alphaAdd = 1
  alphaAddP : w.pt01 L.alphaAdd = w.pt12 (L.alphaMul + 168)
  alphaAddQ : w.pt01 (L.alphaAdd + 1) = w.pt12 (L.alphaMul + 169)
  rkSel : w.qAdd L.rkAdd = 1
  rkP : w.pt01 L.rkAdd = w.pt01 (L.alphaAdd + 2)
  rkQ : w.pt01 (L.rkAdd + 1) = w.pt01 L.ak
  rkX : w.a0 (L.rkAdd + 2) = w.inst 4
  rkY : w.a1 (L.rkAdd + 2) = w.inst 5
  -- `Commit^ivk` (`commit_ivk`)
  b0 : w.ShortRangeCheckRegion L.b0 4
  b2 : w.ShortRangeCheckRegion L.b2 5
  d0 : w.ShortRangeCheckRegion L.d0 9
  hash : w.SinsemillaRegion ivkQ L.hash
  rivkMul : w.FixedMulRegion commitIvkR L.rivkMul
  rivkAddSel : w.qAdd L.rivkAdd = 1
  rivkAddP : w.pt01 L.rivkAdd = w.pt12 (L.rivkMul + 168)
  rivkAddQ : w.pt01 (L.rivkAdd + 1) = w.pt12 (L.rivkMul + 169)
  commitSel : w.qAdd L.commitAdd = 1
  commitP : w.pt01 L.commitAdd = w.pt01 (L.hash + 102)
  commitQ : w.pt01 (L.commitAdd + 1) = w.pt01 (L.rivkAdd + 2)
  aPrime : w.RangeCheckRegion L.aPrime 13
  b2cPrime : w.RangeCheckRegion L.b2cPrime 14
  canon : w.CanonicityRegions L.hash L.b0 L.b2 L.d0 L.aPrime L.b2cPrime L.canonAk L.canonNk
  /-- `ak` in the canonicity gate is a copy of the `x`-coordinate of `ak_P`. -/
  canonAkCopy : w.a0 L.canonAk = w.a0 L.ak
  -- `[ivk] g_d` (`mul`)
  mul : w.MulRegions L.dbl L.inc L.bit0 L.addU0 L.addAcc0 L.bit1 L.addU1 L.addAcc1
    L.bit2 L.addU2 L.addAcc2 L.lsb L.lsbAdd L.sRange L.overflow
  /-- Each region that reads the base holds a copy of the `g_d` cells. -/
  mulBase : w.MulBase (w.pt01 L.gd) L.dbl L.inc L.bit0 L.addU0 L.bit1 L.addU1 L.bit2 L.addU2
    L.lsb
  /-- The scalar of the overflow check is a copy of `ivk`, the `x`-coordinate of the
  commitment. -/
  mulScalar : w.a1 (L.overflow + 1) = w.a0 (L.commitAdd + 2)
  -- `pk_d` (`check_point`, `constrain_instance`)
  pkdSel : w.qPoint L.pkd = 1
  pkdCopy : w.pt01 L.pkd = w.pt01 (L.lsbAdd + 2)
  pkdX : w.a0 L.pkd = w.inst 2
  pkdY : w.a1 L.pkd = w.inst 3

end AddressSignature
