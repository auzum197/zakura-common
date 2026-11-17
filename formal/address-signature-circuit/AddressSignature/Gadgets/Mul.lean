import AddressSignature.Gadgets.MulIncomplete

/-!
# Variable-base scalar multiplication `[ivk] g_d`

`Config::mul` of `chip/ecc.rs`:

1. `acc = [2] base`, by one complete addition;
2. 251 incomplete double-and-add steps for the bits `k_254 … k_4`
   (`MulIncomplete.lean`);
3. three complete bits `k_3, k_2, k_1`: a 2-row gate for the bit and the sign, then
   two complete additions;
4. the least significant bit `k_0`;
5. the overflow check, which makes the decomposition `k = ivk + t_q` canonical.
-/

namespace AddressSignature

open Zcash.Circuits
open Zcash.Circuits.Ecc.Mul (chainNat tQNat)
open Zcash.Circuits.Ecc.Mul.Incomplete.DoubleAndAdd (accScalar)
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD PALLAS_BASE_CARD)
open Point (ext_toSW_iff toSW_add toSW_neg toSW_zero toSW_nsmul
  valid_add valid_neg valid_zero valid_nsmul)

/-! ## Point algebra -/

theorem point_two_nsmul {P : Point Fp} (hP : P.OnCurve) : P + P = 2 • P := by
  have := Point.nsmul_add_one hP 1
  rwa [Ecc.MulFixed.Cert.Chain.one_nsmul_point] at this

/-- One complete double-and-add step: `[a] P + (±P + [a] P) = [2a ± 1] P`. -/
theorem point_step_nsmul {P : Point Fp} (hP : P.OnCurve) (a : ℕ) (ha : 1 ≤ a)
    (bit : Bool) :
    a • P + ((if bit then P else -P) + a • P)
      = (2 * a + (if bit then 1 else 0) * 2 - 1) • P := by
  have hPv : P.Valid := Or.inl hP
  cases bit
  · simp only [Bool.false_eq_true, if_false]
    apply (ext_toSW_iff
      (valid_add (valid_nsmul hPv a) (valid_add (valid_neg hPv) (valid_nsmul hPv a)))
      (valid_nsmul hPv _)).mpr
    rw [toSW_add (valid_nsmul hPv a) (valid_add (valid_neg hPv) (valid_nsmul hPv a)),
      toSW_add (valid_neg hPv) (valid_nsmul hPv a), toSW_neg hPv,
      toSW_nsmul hPv a, toSW_nsmul hPv]
    simpa using Ecc.Mul.nsmul_step (P.toSW hPv) a ha false
  · simp only [if_true]
    apply (ext_toSW_iff
      (valid_add (valid_nsmul hPv a) (valid_add hPv (valid_nsmul hPv a)))
      (valid_nsmul hPv _)).mpr
    rw [toSW_add (valid_nsmul hPv a) (valid_add hPv (valid_nsmul hPv a)),
      toSW_add hPv (valid_nsmul hPv a),
      toSW_nsmul hPv a, toSW_nsmul hPv]
    simpa using Ecc.Mul.nsmul_step (P.toSW hPv) a ha true

theorem point_neg_add_nsmul {P : Point Fp} (hP : P.OnCurve) {m : ℕ} (hm : 1 ≤ m) :
    -P + m • P = (m - 1) • P := by
  have hPv : P.Valid := Or.inl hP
  apply (ext_toSW_iff (valid_add (valid_neg hPv) (valid_nsmul hPv m))
    (valid_nsmul hPv _)).mpr
  rw [toSW_add (valid_neg hPv) (valid_nsmul hPv m), toSW_neg hPv, toSW_nsmul hPv m,
    toSW_nsmul hPv]
  exact Ecc.Mul.neg_add_nsmul (P.toSW hPv) hm

theorem point_zero_add {Q : Point Fp} (hQ : Q.Valid) : (0 : Point Fp) + Q = Q := by
  apply (ext_toSW_iff (valid_add valid_zero hQ) hQ).mpr
  rw [toSW_add valid_zero hQ, toSW_zero, zero_add]

namespace Assignment

variable {w : Assignment} {S : ℕ → Point Fp} {n : ℕ}

/-! ## A complete bit -/

/-- The selectors and internal copy constraints of one complete bit: the region
"variable-base mul (complete bit)" at `ob`, the addition `U + acc` at `ou`, and the
addition `acc + (U + acc)` at `oa`. -/
structure MulCompleteBit (w : Assignment) (ob ou oa : ℕ) : Prop where
  sel : w.qMulComplete ob = 1
  addU : w.qAdd ou = 1
  addAcc : w.qAdd oa = 1
  /-- The `y`-coordinate of `U` is the cell `y_p` of the bit region. -/
  uy : w.a1 ou = w.a2 ob
  /-- Both additions read the same accumulator. -/
  acc : w.pt01 oa = w.pt01 (ou + 1)
  tmp : w.pt01 (oa + 1) = w.pt01 (ou + 2)

theorem mulCompleteBit_sound (h : w.Constrained S n) {ob ou oa : ℕ}
    (hob : ob + 2 ≤ n) (hou : ou + 4 ≤ n) (hoa : oa + 4 ≤ n)
    (hR : w.MulCompleteBit ob ou oa) {P : Point Fp} (hP : P.OnCurve)
    (hbx : w.a0 ou = P.x) (hby : w.a1 ob = P.y) {A : ℕ} (hA : 1 ≤ A)
    (hacc : w.pt01 (ou + 1) = A • P) :
    IsBool (w.a0 (ob + 1) - 2 * w.a0 ob) ∧
      w.pt01 (oa + 2)
        = (2 * A + (if decide (w.a0 (ob + 1) - 2 * w.a0 ob = 1) then 1 else 0) * 2 - 1) • P := by
  have hz : ∀ {p : Fp}, p ∈ w.mulCompletePolys ob → p = 0 := fun hp =>
    h.poly_zero (g := (w.qMulComplete, w.mulCompletePolys)) (by simp [gates]) (r := ob)
      (by omega) (by simp [hR.sel]) hp
  have c0 : boolCheck (w.a0 (ob + 1) - 2 * w.a0 ob) = 0 := hz (by simp [mulCompletePolys])
  have c1 : ternary (w.a0 (ob + 1) - 2 * w.a0 ob) (w.a1 ob - w.a2 ob) (w.a1 ob + w.a2 ob) = 0 :=
    hz (by simp [mulCompletePolys])
  have hbool := isBool_of_boolCheck c0
  refine ⟨hbool, ?_⟩
  have hPv : P.Valid := Or.inl hP
  -- `U` is `P` or `-P`
  have hU : w.pt01 ou
      = if decide (w.a0 (ob + 1) - 2 * w.a0 ob = 1) then P else -P := by
    unfold ternary at c1
    rcases hbool with h0 | h1
    · have hne : ¬ (w.a0 (ob + 1) - 2 * w.a0 ob = 1) := by rw [h0]; exact zero_ne_one
      rw [h0] at c1
      simp only [hne, decide_false, Bool.false_eq_true, if_false]
      show (⟨w.a0 ou, w.a1 ou⟩ : Point Fp) = ⟨P.x, -P.y⟩
      rw [Point.mk.injEq]
      exact ⟨hbx, by rw [hR.uy, ← hby]; linear_combination c1⟩
    · rw [h1] at c1
      simp only [h1, decide_true, if_true]
      show (⟨w.a0 ou, w.a1 ou⟩ : Point Fp) = P
      cases P
      rw [Point.mk.injEq]
      exact ⟨hbx, by rw [hR.uy]; simp only at hby; rw [← hby]; linear_combination -c1⟩
  have hUv : (w.pt01 ou).Valid := by
    rw [hU]; split_ifs
    · exact hPv
    · exact valid_neg hPv
  have haccv : (w.pt01 (ou + 1)).Valid := by rw [hacc]; exact valid_nsmul hPv A
  have htmp := add_sound h (r := ou) (by omega) hR.addU hUv haccv
  have htmpv := add_valid h (r := ou) (by omega) hR.addU hUv haccv
  have hnew := add_sound h (r := oa) (by omega) hR.addAcc (by rw [hR.acc]; exact haccv)
    (by rw [hR.tmp]; exact htmpv)
  rw [hnew, hR.acc, hR.tmp, htmp, hU, hacc]
  exact point_step_nsmul hP A hA _

/-! ## The least significant bit -/

/-- The selectors and internal copy constraint of the least significant bit: the
region at `ol` and the addition `P + acc` at `ola`. -/
structure MulLsb (w : Assignment) (ol ola : ℕ) : Prop where
  sel : w.qMulLsb ol = 1
  add : w.qAdd ola = 1
  p : w.pt01 ola = w.pt12 ol

theorem mulLsb_sound (h : w.Constrained S n) {ol ola : ℕ}
    (hol : ol + 2 ≤ n) (hola : ola + 4 ≤ n) (hR : w.MulLsb ol ola)
    {P : Point Fp} (hP : P.OnCurve)
    (hbx : w.a1 (ol + 1) = P.x) (hby : w.a2 (ol + 1) = P.y) {M : ℕ}
    (hacc : w.pt01 (ola + 1) = M • P) :
    IsBool (w.a0 (ol + 1) - 2 * w.a0 ol) ∧
      w.pt01 (ola + 2)
        = (if decide (w.a0 (ol + 1) - 2 * w.a0 ol = 1) then 0 else -P) + M • P := by
  have hz : ∀ {p : Fp}, p ∈ w.mulLsbPolys ol → p = 0 := fun hp =>
    h.poly_zero (g := (w.qMulLsb, w.mulLsbPolys)) (by simp [gates]) (r := ol)
      (by omega) (by simp [hR.sel]) hp
  have l0 : boolCheck (w.a0 (ol + 1) - w.a0 ol * 2) = 0 := hz (by simp [mulLsbPolys])
  have l1 : ternary (w.a0 (ol + 1) - w.a0 ol * 2) (w.a1 ol) (w.a1 ol - w.a1 (ol + 1)) = 0 :=
    hz (by simp [mulLsbPolys])
  have l2 : ternary (w.a0 (ol + 1) - w.a0 ol * 2) (w.a2 ol) (w.a2 ol + w.a2 (ol + 1)) = 0 :=
    hz (by simp [mulLsbPolys])
  have hcomm : w.a0 (ol + 1) - w.a0 ol * 2 = w.a0 (ol + 1) - 2 * w.a0 ol := by ring
  rw [hcomm] at l0 l1 l2
  have hbool := isBool_of_boolCheck l0
  refine ⟨hbool, ?_⟩
  have hPv : P.Valid := Or.inl hP
  have hp : w.pt12 ol
      = if decide (w.a0 (ol + 1) - 2 * w.a0 ol = 1) then 0 else -P := by
    unfold ternary at l1 l2
    rcases hbool with h0 | h1
    · have hne : ¬ (w.a0 (ol + 1) - 2 * w.a0 ol = 1) := by rw [h0]; exact zero_ne_one
      rw [h0] at l1 l2
      simp only [hne, decide_false, Bool.false_eq_true, if_false]
      show (⟨w.a1 ol, w.a2 ol⟩ : Point Fp) = ⟨P.x, -P.y⟩
      rw [Point.mk.injEq, ← hbx, ← hby]
      exact ⟨by linear_combination l1, by linear_combination l2⟩
    · rw [h1] at l1 l2
      simp only [h1, decide_true, if_true]
      show (⟨w.a1 ol, w.a2 ol⟩ : Point Fp) = ⟨0, 0⟩
      rw [Point.mk.injEq]
      exact ⟨by linear_combination l1, by linear_combination l2⟩
  have hpv : (w.pt12 ol).Valid := by
    rw [hp]; split_ifs
    · exact valid_zero
    · exact valid_neg hPv
  have hres := add_sound h (r := ola) (by omega) hR.add (by rw [hR.p]; exact hpv)
    (by rw [hacc]; exact valid_nsmul hPv M)
  rw [hres, hR.p, hp, hacc]

end Assignment

end AddressSignature
