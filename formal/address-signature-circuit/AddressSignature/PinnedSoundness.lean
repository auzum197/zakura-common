import AddressSignature.PinnedCheck
import AddressSignature.Soundness

/-!
# Soundness for the constraint system of the pinned description

The model in `Gates.lean` has 13 binary selectors, as the Rust code does before key
generation. Halo 2 packs them into the fixed columns 13, 14, 15, and the pinned
description contains the packed form. This file states the constraint system in the
packed form, with the polynomials of `Pinned.lean`, and proves that it implies the
constraint system of the model. The soundness theorem follows for the packed form.
-/

namespace AddressSignature

open Zcash.Circuits

/-- The three fixed columns that hold the packed selectors. On each row, a column
holds 0, or the index of the one selector of the column that is enabled. -/
structure PackedSelectors where
  s13 : ℕ → Fp
  s14 : ℕ → Fp
  s15 : ℕ → Fp

namespace Pinned

/-- The 15 gates of the pinned description: for each, the selector expression and
the constraints. -/
def gates (w : Assignment) (c : PackedSelectors) : List ((ℕ → Fp) × (ℕ → List Fp)) :=
  [ (fun r => pointSelector (c.s13 r), pointPolys w),
    (fun r => addSelector (c.s13 r), addPolys w),
    (fun r => fixedWindowSelector (w.fixedZPlusOne r), fixedWindowPolys w),
    (fun r => fixedAddSelector (c.s13 r), fixedAddPolys w),
    (fun r => mul1Selector (c.s13 r), mul1Polys w),
    (fun r => mul2Selector (c.s14 r), mul2Polys w),
    (fun r => mul3Selector (c.s14 r), mul3Polys w),
    (fun r => mulCompleteSelector (c.s14 r), mulCompletePolys w),
    (fun r => mulLsbSelector (c.s14 r), mulLsbPolys w),
    (fun r => mulOverflowSelector (c.s14 r), mulOverflowPolys w),
    (fun r => sinInitSelector (c.s15 r), sinInitPolys w),
    (fun r => sinSelector (w.fLookup r), sinPolys w),
    (fun r => shiftSelector (c.s15 r), shiftPolys w),
    (fun r => commitIvkAkSelector (c.s15 r), commitIvkAkPolys w),
    (fun r => commitIvkNkSelector (c.s15 r), commitIvkNkPolys w) ]

/-- The constraint system of the pinned description holds on the first `n` rows. -/
structure Constrained (w : Assignment) (c : PackedSelectors) (n : ℕ) : Prop where
  gates : ∀ g ∈ gates w c, Assignment.GateHolds n g
  /-- The lookup: the three input expressions are a row of the generator table. -/
  lookup : ∀ r, r < n → ∃ i : ℕ, i < 2 ^ 10 ∧
    lookupIndex w r = (i : Fp) ∧ lookupX w r = (generators.S i).x ∧
    lookupY w r = (generators.S i).y

end Pinned

/-- The binary selectors of the model are the indicators of the packed columns: a
selector is 1 on the rows where its packed column holds its index. The indices are
those of `Pinned.selectorTable`. -/
structure SelectorsPacked (w : Assignment) (c : PackedSelectors) : Prop where
  qPoint : ∀ r, w.qPoint r = if c.s13 r = 1 then 1 else 0
  qAdd : ∀ r, w.qAdd r = if c.s13 r = 2 then 1 else 0
  qFixedAdd : ∀ r, w.qFixedAdd r = if c.s13 r = 3 then 1 else 0
  qMul1 : ∀ r, w.qMul1 r = if c.s13 r = 4 then 1 else 0
  qMul2 : ∀ r, w.qMul2 r = if c.s14 r = 1 then 1 else 0
  qMul3 : ∀ r, w.qMul3 r = if c.s14 r = 2 then 1 else 0
  qMulComplete : ∀ r, w.qMulComplete r = if c.s14 r = 3 then 1 else 0
  qMulLsb : ∀ r, w.qMulLsb r = if c.s14 r = 4 then 1 else 0
  qMulOverflow : ∀ r, w.qMulOverflow r = if c.s14 r = 5 then 1 else 0
  qSinInit : ∀ r, w.qSinInit r = if c.s15 r = 1 then 1 else 0
  qShift : ∀ r, w.qShift r = if c.s15 r = 2 then 1 else 0
  qCommitIvkAk : ∀ r, w.qCommitIvkAk r = if c.s15 r = 3 then 1 else 0
  qCommitIvkNk : ∀ r, w.qCommitIvkNk r = if c.s15 r = 4 then 1 else 0

/-- A gate of the description with a packed selector implies the gate of the model
with the binary selector. -/
theorem gateHolds_of_packed {n : ℕ} {sel : Fp → Fp} {col q : ℕ → Fp}
    {polys polys' : ℕ → List Fp} {idx : Fp}
    (h : Assignment.GateHolds n (fun r => sel (col r), polys'))
    (hp : ∀ r, polys' r = polys r) (hne : sel idx ≠ 0)
    (hq : ∀ r, q r = if col r = idx then 1 else 0) :
    Assignment.GateHolds n (q, polys) := by
  intro r hr p hp'
  show q r * p = 0
  rw [hq r]
  split_ifs with hcol
  · have := h r hr p (by show p ∈ polys' r; rw [hp r]; exact hp')
    simp only [hcol] at this
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hne
    · rw [h0, mul_zero]
  · rw [zero_mul]

/-- The constraint system of the pinned description implies the constraint system
of the model. -/
theorem constrained_of_pinned {w : Assignment} {c : PackedSelectors} {n : ℕ}
    (hP : Pinned.Constrained w c n) (hS : SelectorsPacked w c) :
    w.Constrained generators.S n := by
  have hg : ∀ g, g ∈ Pinned.gates w c → Assignment.GateHolds n g := hP.gates
  refine ⟨?_, ?_⟩
  · intro g hmem
    simp only [Assignment.gates, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · exact gateHolds_of_packed (hg _ (by simp [Pinned.gates])) (pointPolys_eq w)
        pointSelector_ne hS.qPoint
    · exact gateHolds_of_packed (hg _ (by simp [Pinned.gates])) (addPolys_eq w)
        addSelector_ne hS.qAdd
    · intro r hr p hp
      have := hg (fun r => Pinned.fixedWindowSelector (w.fixedZPlusOne r),
        Pinned.fixedWindowPolys w) (by simp [Pinned.gates]) r hr p
        (by show p ∈ Pinned.fixedWindowPolys w r; rw [fixedWindowPolys_eq]; exact hp)
      exact this
    · exact gateHolds_of_packed (hg _ (by simp [Pinned.gates])) (fixedAddPolys_eq w)
        fixedAddSelector_ne hS.qFixedAdd
    · exact gateHolds_of_packed (hg _ (by simp [Pinned.gates])) (mul1Polys_eq w)
        mul1Selector_ne hS.qMul1
    · exact gateHolds_of_packed (hg _ (by simp [Pinned.gates])) (mul2Polys_eq w)
        mul2Selector_ne hS.qMul2
    · exact gateHolds_of_packed (hg _ (by simp [Pinned.gates])) (mul3Polys_eq w)
        mul3Selector_ne hS.qMul3
    · exact gateHolds_of_packed (hg _ (by simp [Pinned.gates])) (mulCompletePolys_eq w)
        mulCompleteSelector_ne hS.qMulComplete
    · exact gateHolds_of_packed (hg _ (by simp [Pinned.gates])) (mulLsbPolys_eq w)
        mulLsbSelector_ne hS.qMulLsb
    · exact gateHolds_of_packed (hg _ (by simp [Pinned.gates])) (mulOverflowPolys_eq w)
        mulOverflowSelector_ne hS.qMulOverflow
    · exact gateHolds_of_packed (hg _ (by simp [Pinned.gates])) (sinInitPolys_eq w)
        sinInitSelector_ne hS.qSinInit
    · intro r hr p hp
      have := hg (fun r => Pinned.sinSelector (w.fLookup r), Pinned.sinPolys w)
        (by simp [Pinned.gates]) r hr p (by show p ∈ Pinned.sinPolys w r; rw [sinPolys_eq]; exact hp)
      simp only [sinSelector_eq] at this
      exact this
    · exact gateHolds_of_packed (hg _ (by simp [Pinned.gates])) (shiftPolys_eq w)
        shiftSelector_ne hS.qShift
    · exact gateHolds_of_packed (hg _ (by simp [Pinned.gates])) (commitIvkAkPolys_eq w)
        commitIvkAkSelector_ne hS.qCommitIvkAk
    · exact gateHolds_of_packed (hg _ (by simp [Pinned.gates])) (commitIvkNkPolys_eq w)
        commitIvkNkSelector_ne hS.qCommitIvkNk
  · intro r hr
    obtain ⟨i, hi, h1, h2, h3⟩ := hP.lookup r hr
    exact ⟨i, hi, by rw [← lookupIndex_eq]; exact h1, by rw [← lookupX_eq]; exact h2,
      by rw [← lookupY_eq]; exact h3⟩

/-- **Soundness for the pinned description.** If an assignment satisfies the gates
and the lookup of the pinned circuit description, with the packed selector columns
`c`, and the fixed cells and copy constraints are those of `Circuit::synthesize`,
the primary input satisfies the Address signature statement. -/
theorem soundness_pinned (w : Assignment) (c : PackedSelectors) (L : Placement) (n : ℕ)
    (hP : Pinned.Constrained w c n) (hS : SelectorsPacked w c) (hW : Wired w L n) :
    Statement ⟨w.inst 0, w.inst 1⟩ ⟨w.inst 2, w.inst 3⟩ ⟨w.inst 4, w.inst 5⟩ :=
  soundness w L n (constrained_of_pinned hP hS) hW

open Zcash.Circuits.Specs.Sinsemilla (HashGuarded commitIvkChunks) in
/-- **Soundness for the pinned description, with the witness in named cells.**

This is the main theorem of the project. It is `soundness_explicit` for the
constraint system of the pinned circuit description. -/
theorem soundness_pinned_explicit (w : Assignment) (c : PackedSelectors) (L : Placement)
    (n : ℕ) (hP : Pinned.Constrained w c n) (hS : SelectorsPacked w c) (hW : Wired w L n) :
    (⟨w.inst 0, w.inst 1⟩ : Point Fp) = w.pt01 L.gd ∧
    (⟨w.inst 2, w.inst 3⟩ : Point Fp) = w.pt01 L.pkd ∧
    (⟨w.inst 4, w.inst 5⟩ : Point Fp) = w.pt01 (L.rkAdd + 2) ∧
    (w.pt01 L.gd).OnCurve ∧ (w.pt01 L.pkd).OnCurve ∧ (w.pt01 L.ak).OnCurve ∧
    ∃ (alpha rivk : Fq),
      w.pt01 (L.alphaAdd + 2) = alpha • spendAuthG ∧
      w.pt01 (L.rivkAdd + 2) = rivk • commitIvkR ∧
      w.pt01 (L.rkAdd + 2) = alpha • spendAuthG + w.pt01 L.ak ∧
      HashGuarded generators.S ivkQ
        (commitIvkChunks (w.pt01 L.ak).x.val (w.a0 L.canonNk).val)
        (fun hashPoint => w.a0 (L.commitAdd + 2) = (hashPoint + rivk • commitIvkR).x) ∧
      w.pt01 L.pkd = (w.a0 (L.commitAdd + 2)).val • w.pt01 L.gd :=
  soundness_explicit w L n (constrained_of_pinned hP hS) hW

end AddressSignature
