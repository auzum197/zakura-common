import AddressSignature.Pinned
import AddressSignature.Spec

/-!
# The model has the polynomials of the pinned circuit description

`Pinned.lean` is generated from the pinned description of the verifying key,
`crates/orchard/src/circuit_data/circuit_description_address_signature_v1`. This file
proves, for each of the 15 gates, that the constraint polynomials of the description
are equal to the constraint polynomials of the model in `Gates.lean`, and that the
three input expressions of the lookup are equal.

It also proves that the selector expression of each gate, which Halo 2 creates when
it packs the 13 binary selectors into 3 fixed columns, is not zero for the value that
enables the gate.
-/

namespace AddressSignature

open Zcash.Circuits

/-- `pallas::Base::TWO_INV` as a number. -/
theorem twoInv_eq : Assignment.twoInv
    = (14474011154664524427946373126085988481681528240970780357977338382174983815169 : Fp) := by
  have h : (2 : Fp)
      * (14474011154664524427946373126085988481681528240970780357977338382174983815169 : Fp)
      = 1 := by decide
  exact (eq_inv_of_mul_eq_one_right h).symm

/-- The lookup defaults to the first row of the generator table. -/
theorem initX_eq : Pinned.initX = (generators.S 0).x := by decide +kernel

theorem initY_eq : Pinned.initY = (generators.S 0).y := by decide +kernel

/-- Splits an equality of two lists of polynomials and proves each by `ring`. -/
macro "pinned_polys" : tactic =>
  `(tactic| (simp only [List.cons.injEq, and_true]; and_intros <;> first | ring | exact True.intro))

variable (w : Assignment) (r : ℕ)

theorem pointPolys_eq : Pinned.pointPolys w r = w.pointPolys r := by
  simp only [Pinned.pointPolys, Assignment.pointPolys, pallasB]
  pinned_polys

theorem addPolys_eq : Pinned.addPolys w r = w.addPolys r := by
  simp only [Pinned.addPolys, Assignment.addPolys]
  pinned_polys

theorem fixedWindowPolys_eq : Pinned.fixedWindowPolys w r = w.fixedWindowPolys r := by
  simp only [Pinned.fixedWindowPolys, Assignment.fixedWindowPolys, Assignment.interpolatedX,
    Assignment.rangeCheck8, pallasB]
  pinned_polys

theorem fixedAddPolys_eq : Pinned.fixedAddPolys w r = w.fixedAddPolys r := by
  simp only [Pinned.fixedAddPolys, Assignment.fixedAddPolys]
  pinned_polys

theorem mul1Polys_eq : Pinned.mul1Polys w r = w.mul1Polys r := by
  simp only [Pinned.mul1Polys, Assignment.mul1Polys, Assignment.yA, Assignment.bigYA,
    Assignment.xR, twoInv_eq]
  pinned_polys

theorem mul2Polys_eq : Pinned.mul2Polys w r = w.mul2Polys r := by
  simp only [Pinned.mul2Polys, Assignment.mul2Polys, Assignment.mulLoopPolys, Assignment.yA,
    Assignment.bigYA, Assignment.xR, Assignment.boolCheck, twoInv_eq, List.cons_append,
    List.nil_append]
  pinned_polys

theorem mul3Polys_eq : Pinned.mul3Polys w r = w.mul3Polys r := by
  simp only [Pinned.mul3Polys, Assignment.mul3Polys, Assignment.mulLoopPolys, Assignment.yA,
    Assignment.bigYA, Assignment.xR, Assignment.boolCheck, twoInv_eq]
  pinned_polys

theorem mulCompletePolys_eq : Pinned.mulCompletePolys w r = w.mulCompletePolys r := by
  simp only [Pinned.mulCompletePolys, Assignment.mulCompletePolys, Assignment.boolCheck,
    Assignment.ternary]
  pinned_polys

theorem mulLsbPolys_eq : Pinned.mulLsbPolys w r = w.mulLsbPolys r := by
  simp only [Pinned.mulLsbPolys, Assignment.mulLsbPolys, Assignment.boolCheck,
    Assignment.ternary]
  pinned_polys

theorem mulOverflowPolys_eq : Pinned.mulOverflowPolys w r = w.mulOverflowPolys r := by
  simp only [Pinned.mulOverflowPolys, Assignment.mulOverflowPolys, Ecc.tQ]
  pinned_polys

theorem sinInitPolys_eq : Pinned.sinInitPolys w r = w.sinInitPolys r := by
  simp only [Pinned.sinInitPolys, Assignment.sinInitPolys, Assignment.bigYA, Assignment.xR]
  pinned_polys

theorem sinPolys_eq : Pinned.sinPolys w r = w.sinPolys r := by
  simp only [Pinned.sinPolys, Assignment.sinPolys, Assignment.bigYA, Assignment.xR,
    Assignment.qS3, Assignment.fS2]
  pinned_polys

theorem shiftPolys_eq : Pinned.shiftPolys w r = w.shiftPolys r := by
  simp only [Pinned.shiftPolys, Assignment.shiftPolys]
  pinned_polys

theorem commitIvkAkPolys_eq : Pinned.commitIvkAkPolys w r = w.commitIvkAkPolys r := by
  simp only [Pinned.commitIvkAkPolys, Assignment.commitIvkAkPolys, Assignment.boolCheck, tP]
  pinned_polys

theorem commitIvkNkPolys_eq : Pinned.commitIvkNkPolys w r = w.commitIvkNkPolys r := by
  simp only [Pinned.commitIvkNkPolys, Assignment.commitIvkNkPolys, Assignment.boolCheck, tP]
  pinned_polys

theorem lookupIndex_eq : Pinned.lookupIndex w r = w.lookupIndex r := by
  simp only [Pinned.lookupIndex, Assignment.lookupIndex, Assignment.fSin, Assignment.fRc,
    Assignment.qRun, Assignment.qS3, Assignment.fS2, twoInv_eq]
  ring

theorem lookupX_eq : Pinned.lookupX w r = w.lookupX (generators.S 0).x r := by
  rw [← initX_eq]
  simp only [Pinned.lookupX, Pinned.initX, Assignment.lookupX, Assignment.fSin, Assignment.fRc,
    twoInv_eq]
  ring

theorem lookupY_eq : Pinned.lookupY w r = w.lookupY (generators.S 0).y r := by
  rw [← initY_eq]
  simp only [Pinned.lookupY, Pinned.initY, Assignment.lookupY, Assignment.fSin, Assignment.fRc,
    Assignment.sinYP, Assignment.bigYA, Assignment.xR, twoInv_eq]
  ring

/-- The selector expression of the Sinsemilla gate is `f_sin`. -/
theorem sinSelector_eq : Pinned.sinSelector (w.fLookup r) = w.fSin r := by
  simp only [Pinned.sinSelector, Assignment.fSin]
  ring

/-! ## The packed selectors

Halo 2 packs the 13 binary selectors into the fixed columns 13, 14, 15. A packed
column holds 0, or the index of the one selector that is enabled on the row. The
selector expression of a gate is not zero for the index of its selector. -/

theorem pointSelector_ne : Pinned.pointSelector 1 ≠ 0 := by decide
theorem addSelector_ne : Pinned.addSelector 2 ≠ 0 := by decide
theorem fixedAddSelector_ne : Pinned.fixedAddSelector 3 ≠ 0 := by decide
theorem mul1Selector_ne : Pinned.mul1Selector 4 ≠ 0 := by decide
theorem mul2Selector_ne : Pinned.mul2Selector 1 ≠ 0 := by decide
theorem mul3Selector_ne : Pinned.mul3Selector 2 ≠ 0 := by decide
theorem mulCompleteSelector_ne : Pinned.mulCompleteSelector 3 ≠ 0 := by decide
theorem mulLsbSelector_ne : Pinned.mulLsbSelector 4 ≠ 0 := by decide
theorem mulOverflowSelector_ne : Pinned.mulOverflowSelector 5 ≠ 0 := by decide
theorem sinInitSelector_ne : Pinned.sinInitSelector 1 ≠ 0 := by decide
theorem shiftSelector_ne : Pinned.shiftSelector 2 ≠ 0 := by decide
theorem commitIvkAkSelector_ne : Pinned.commitIvkAkSelector 3 ≠ 0 := by decide
theorem commitIvkNkSelector_ne : Pinned.commitIvkNkSelector 4 ≠ 0 := by decide

/-- The selector of the fixed-base window gate is the column `fixed_z_plus_one`. -/
theorem fixedWindowSelector_eq (f : Fp) : Pinned.fixedWindowSelector f = f := rfl

/-- The enabling values agree with the table that the generator script computes. -/
theorem selectorTable_eq : Pinned.selectorTable =
    [ ("point", 13, some 1), ("add", 13, some 2), ("fixedWindow", 8, none),
      ("fixedAdd", 13, some 3), ("mul1", 13, some 4), ("mul2", 14, some 1),
      ("mul3", 14, some 2), ("mulComplete", 14, some 3), ("mulLsb", 14, some 4),
      ("mulOverflow", 14, some 5), ("sinInit", 15, some 1), ("sin", 9, some 1),
      ("shift", 15, some 2), ("commitIvkAk", 15, some 3), ("commitIvkNk", 15, some 4) ] := rfl

end AddressSignature
