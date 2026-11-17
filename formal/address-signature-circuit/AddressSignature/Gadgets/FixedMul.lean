import AddressSignature.Gadgets.Add

/-!
# Fixed-base scalar multiplication

`Config::mul_fixed` of `chip/ecc.rs`: 85 windows of 3 bits, 2 rows each, then one
complete addition for the last window.

The fixed-base window gate uses the fixed column `fixed_z_plus_one` as its selector
(shortcut 1), and reads the eight Lagrange columns on the same row.
-/

namespace AddressSignature

open Zcash.Circuits
open Zcash.Circuits.Ecc.MulFixed (FixedBase CoordsParams windowPoint partialSum)
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)

/-- `range_check(word, 8) = 0` constrains the word to `0..7`. -/
theorem rangeCheck8_zero {v : Fp} (h : Assignment.rangeCheck8 v = 0) :
    ∃ k : ℕ, k < 8 ∧ v = (k : Fp) := by
  unfold Assignment.rangeCheck8 at h
  simp only [mul_eq_zero] at h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h) | h
  · exact ⟨0, by norm_num, by simpa using h⟩
  · exact ⟨1, by norm_num, by push_cast; linear_combination -h⟩
  · exact ⟨2, by norm_num, by push_cast; linear_combination -h⟩
  · exact ⟨3, by norm_num, by push_cast; linear_combination -h⟩
  · exact ⟨4, by norm_num, by push_cast; linear_combination -h⟩
  · exact ⟨5, by norm_num, by push_cast; linear_combination -h⟩
  · exact ⟨6, by norm_num, by push_cast; linear_combination -h⟩
  · exact ⟨7, by norm_num, by push_cast; linear_combination -h⟩

namespace Assignment

variable {w : Assignment} {S : ℕ → Point Fp} {n : ℕ}

/-- The fixed cells that the window gate reads on row `r`: `z` (from the selector
column `fixed_z_plus_one`) and the eight Lagrange coefficients. -/
def rowParams (w : Assignment) (r : ℕ) : CoordsParams Fp where
  z := w.fixedZPlusOne r - 1
  lagrange0 := w.lagrange 0 r
  lagrange1 := w.lagrange 1 r
  lagrange2 := w.lagrange 2 r
  lagrange3 := w.lagrange 3 r
  lagrange4 := w.lagrange 4 r
  lagrange5 := w.lagrange 5 r
  lagrange6 := w.lagrange 6 r
  lagrange7 := w.lagrange 7 r

/-- The fixed cells and copy constraints of the region "fixed-base mul (incomplete
addition)" for the base `B`, placed at row `o`. -/
structure FixedMulRegion (w : Assignment) (B : FixedBase) (o : ℕ) : Prop where
  /-- Window `j` is on row `o + 2 j`. Its fixed cells hold `z + 1` and the Lagrange
  coefficients of the window. -/
  params : ∀ j, j < 85 → w.rowParams (o + 2 * j) = B.params j
  /-- Windows 1 to 83 enable `q_fixed_add`. -/
  fixedAdd : ∀ j, 1 ≤ j → j ≤ 83 → w.qFixedAdd (o + 2 * j) = 1
  /-- The accumulator before window 1 is a copy of the point of window 0. -/
  copyX : w.a1 (o + 3) = w.a1 o
  copyY : w.a2 (o + 3) = w.a2 o

/-- The fixed-base window gate on one window row: the window is 3 bits and the
point is the table point of the window. -/
theorem fixedWindow_sound (h : w.Constrained S n) (B : FixedBase) {j r : ℕ}
    (hj : j < 85) (hr : r < n) (hz : (B.params j).z + 1 ≠ 0)
    (hparams : w.rowParams r = B.params j) :
    ∃ k : ℕ, k < 8 ∧ w.a0 r = (k : Fp) ∧ w.pt12 r = windowPoint B.point j k := by
  have hzval : w.fixedZPlusOne r - 1 = (B.params j).z := congrArg CoordsParams.z hparams
  have hsel : w.fixedZPlusOne r ≠ 0 := by
    intro h0
    apply hz
    rw [← hzval, h0]
    ring
  have hzero : ∀ {p : Fp}, p ∈ w.fixedWindowPolys r → p = 0 := fun hp =>
    h.poly_zero (g := (w.fixedZPlusOne, w.fixedWindowPolys)) (by simp [gates]) hr hsel hp
  have hx : w.interpolatedX r - w.a1 r = 0 := hzero (by simp [fixedWindowPolys])
  have hu : w.a0 (r + 1) * w.a0 (r + 1) - w.a2 r - (w.fixedZPlusOne r - 1) = 0 :=
    hzero (by simp [fixedWindowPolys])
  have hc : w.a2 r * w.a2 r - w.a1 r * w.a1 r * w.a1 r - pallasB = 0 :=
    hzero (by simp [fixedWindowPolys])
  have hrange : rangeCheck8 (w.a0 r) = 0 := hzero (by simp [fixedWindowPolys])
  obtain ⟨k, hk, hwin⟩ := rangeCheck8_zero hrange
  refine ⟨k, hk, hwin, ?_⟩
  have hspec : Ecc.MulFixed.Coords.Spec (B.params j)
      { window := w.a0 r, xP := w.a1 r, yP := w.a2 r, u := w.a0 (r + 1) } := by
    rw [← hparams]
    refine ⟨?_, ?_, ?_⟩
    · show w.a1 r = Ecc.MulFixed.interpolate (w.rowParams r) (w.a0 r)
      have : Ecc.MulFixed.interpolate (w.rowParams r) (w.a0 r) = w.interpolatedX r := rfl
      rw [this]
      linear_combination -hx
    · show w.a0 (r + 1) * w.a0 (r + 1) = w.a2 r + (w.fixedZPlusOne r - 1)
      linear_combination hu
    · show w.a2 r * w.a2 r = w.a1 r * w.a1 r * w.a1 r + pallasB
      linear_combination hc
  obtain ⟨h1, h2⟩ := B.coords_eq_windowPoint hj hk (row :=
    { window := w.a0 r, xP := w.a1 r, yP := w.a2 r, u := w.a0 (r + 1) }) hwin hspec
  show (⟨w.a1 r, w.a2 r⟩ : Point Fp) = _
  rw [Point.mk.injEq]
  exact ⟨h1, h2⟩

/-- Gate "fixed-base incomplete addition" on row `r`: if the window point `P` (row
`r`) and the accumulator `Q` (row `r + 1`) are on the curve and have different
`x`-coordinates, the point in row `r + 3` is `P + Q`. -/
theorem fixedAdd_sound (h : w.Constrained S n) {r : ℕ} (hr : r < n)
    (hsel : w.qFixedAdd r = 1)
    (hP : (w.pt12 r).OnCurve) (hQ : (w.pt12 (r + 1)).OnCurve)
    (hne : w.a1 r ≠ w.a1 (r + 1)) :
    w.pt12 (r + 3) = w.pt12 r + w.pt12 (r + 1) := by
  have hzero : ∀ {p : Fp}, p ∈ w.fixedAddPolys r → p = 0 := fun hp =>
    h.poly_zero (g := (w.qFixedAdd, w.fixedAddPolys)) (by simp [gates]) hr
      (by simp [hsel]) hp
  have hadd := Ecc.AddIncomplete.Gate.eq_nondegenerateAdd_of_polys_zero
    (p := w.pt12 r) (q := w.pt12 (r + 1)) (r := w.pt12 (r + 3)) hne
    ⟨hzero (by simp [fixedAddPolys, Ecc.AddIncomplete.Gate.poly1,
        Ecc.AddIncomplete.Gate.Input.fromPoints, pt12]),
      hzero (by simp [fixedAddPolys, Ecc.AddIncomplete.Gate.poly2,
        Ecc.AddIncomplete.Gate.Input.fromPoints, pt12])⟩
  rw [hadd]
  exact Point.nondegenerateAdd_eq_add (Point.ne_zero_of_onCurve hP)
    (Point.ne_zero_of_onCurve hQ) hne

/-- The windows of a region: each window is 3 bits and its row holds the table
point. -/
theorem fixedMulRegion_windows (h : w.Constrained S n) (B : FixedBase)
    (hz : ∀ j, j < 85 → (B.params j).z + 1 ≠ 0) {o : ℕ} (ho : o + 170 ≤ n)
    (hR : w.FixedMulRegion B o) :
    ∃ ks : ℕ → ℕ, (∀ j, ks j < 8) ∧
      ∀ j, j < 85 → w.pt12 (o + 2 * j) = windowPoint B.point j (ks j) := by
  have hwin : ∀ j, ∃ k : ℕ, k < 8 ∧
      (j < 85 → w.pt12 (o + 2 * j) = windowPoint B.point j k) := by
    intro j
    by_cases hj : j < 85
    · obtain ⟨k, hk, -, hpt⟩ := fixedWindow_sound h B hj (r := o + 2 * j) (by omega)
        (hz j hj) (hR.params j hj)
      exact ⟨k, hk, fun _ => hpt⟩
    · exact ⟨0, by norm_num, fun h' => absurd h' hj⟩
  choose ks hks hpt using hwin
  exact ⟨ks, hks, hpt⟩

/-- The accumulator of a region after windows `0..j`, for `j ≤ 83`. It is in the
second row of window `j + 1`. -/
theorem fixedMulRegion_acc (h : w.Constrained S n) (B : FixedBase) {o : ℕ}
    (ho : o + 170 ≤ n) (hR : w.FixedMulRegion B o) (ks : ℕ → ℕ) (hks : ∀ j, ks j < 8)
    (hpt : ∀ j, j < 85 → w.pt12 (o + 2 * j) = windowPoint B.point j (ks j)) :
    ∀ j, j ≤ 83 → w.pt12 (o + 2 * j + 3) = partialSum ks j • B.point := by
  have hlow : ∀ j, j < 84 → w.pt12 (o + 2 * j) = ((ks j + 2) * 8 ^ j) • B.point := by
    intro j hj
    rw [hpt j (by omega), Ecc.MulFixed.windowPoint_lower B.point hj (hks j)]
  intro j
  induction j with
  | zero =>
    intro _
    have h0 := hlow 0 (by norm_num)
    have hcopy : w.pt12 (o + 2 * 0 + 3) = w.pt12 (o + 2 * 0) := by
      show (⟨w.a1 (o + 2 * 0 + 3), w.a2 (o + 2 * 0 + 3)⟩ : Point Fp)
        = ⟨w.a1 (o + 2 * 0), w.a2 (o + 2 * 0)⟩
      rw [Point.mk.injEq]
      exact ⟨hR.copyX, hR.copyY⟩
    rw [hcopy, h0]
    simp [partialSum]
  | succ i ih =>
    intro hi
    have hacc := ih (by omega)
    have hwp := hlow (i + 1) (by omega)
    obtain ⟨t, ht⟩ : ∃ t : ℕ, t = (ks (i + 1) + 2) * 8 ^ (i + 1) := ⟨_, rfl⟩
    obtain ⟨s, hs⟩ : ∃ s : ℕ, s = partialSum ks i := ⟨_, rfl⟩
    rw [← ht] at hwp
    rw [← hs] at hacc
    have hs_lt : s < 2 * 8 ^ (i + 1) := by
      rw [hs]; exact Ecc.MulFixed.partialSum_lt _ i (fun _ _ => hks _)
    have hs_pos : 0 < s := by rw [hs]; exact Ecc.MulFixed.partialSum_pos _ _
    obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ :=
      Ecc.MulFixed.step_bounds (hks (i + 1)) hs_lt hs_pos (by omega)
    rw [← ht] at hb1 hb2 hb3 hb5
    have hidx : o + 2 * (i + 1) + 1 = o + 2 * i + 3 := by omega
    have hidx' : o + 2 * (i + 1) + 3 = o + 2 * (i + 1) + 3 := rfl
    have hP : (w.pt12 (o + 2 * (i + 1))).OnCurve := by
      rw [hwp]; exact Point.nsmul_onCurve B.onCurve hb1 hb3
    have hQ : (w.pt12 (o + 2 * (i + 1) + 1)).OnCurve := by
      rw [hidx, hacc]; exact Point.nsmul_onCurve B.onCurve hs_pos hb4
    have hne : w.a1 (o + 2 * (i + 1)) ≠ w.a1 (o + 2 * (i + 1) + 1) := by
      have h1 : w.a1 (o + 2 * (i + 1)) = (t • B.point).x := congrArg Point.x hwp
      have h2 : w.a1 (o + 2 * (i + 1) + 1) = (s • B.point).x := by
        rw [hidx]; exact congrArg Point.x hacc
      rw [h1, h2]
      exact Point.nsmul_x_ne B.onCurve hs_pos hb2 (by omega)
    have hstep := fixedAdd_sound h (r := o + 2 * (i + 1)) (by omega)
      (hR.fixedAdd (i + 1) (by omega) (by omega)) hP hQ hne
    rw [hstep, hidx, hwp, hacc, Point.nsmul_add_nsmul B.onCurve]
    have hps : t + s = partialSum ks (i + 1) := by
      rw [ht, hs, Ecc.MulFixed.partialSum_succ]; ring
    rw [hps]

/-- The region "fixed-base mul (incomplete addition)": there are 85 windows `ks`,
each below 8, such that row 168 holds the table point of the last window and row
169 holds the accumulator of windows 0 to 83. -/
theorem fixedMulRegion_sound (h : w.Constrained S n) (B : FixedBase)
    (hz : ∀ j, j < 85 → (B.params j).z + 1 ≠ 0) {o : ℕ} (ho : o + 170 ≤ n)
    (hR : w.FixedMulRegion B o) :
    ∃ ks : ℕ → ℕ, (∀ j, ks j < 8) ∧
      w.pt12 (o + 168) = windowPoint B.point 84 (ks 84) ∧
      w.pt12 (o + 169) = partialSum ks 83 • B.point := by
  obtain ⟨ks, hks, hpt⟩ := fixedMulRegion_windows h B hz ho hR
  exact ⟨ks, hks, hpt 84 (by norm_num), fixedMulRegion_acc h B ho hR ks hks hpt 83 le_rfl⟩

/-- The scalar that 85 windows encode. It is not reduced: it can be any integer
below `2^255`. -/
def windowsScalar (ks : ℕ → ℕ) : CompElliptic.Fields.Pasta.Fq :=
  ((∑ j ∈ Finset.range 85, ks j * 8 ^ j : ℕ) : CompElliptic.Fields.Pasta.Fq)

/-- The last window point plus the accumulator is the scalar multiple. -/
theorem windowPoint_add_partialSum (B : FixedBase) (ks : ℕ → ℕ) :
    windowPoint B.point 84 (ks 84) + partialSum ks 83 • B.point
      = (windowsScalar ks) • B := by
  unfold windowPoint
  rw [Point.nsmul_add_nsmul B.onCurve, ← B.add_natCast_val_nsmul,
    Ecc.MulFixed.BaseFieldElem.RunningSumMul.windowScalar_partialSum]
  rfl

/-- `Config::mul_fixed`: the region of 85 windows at row `o`, and the complete
addition of the last window at row `oa`. The result is `[α] B` for a scalar `α`. -/
theorem fixedMul_sound (h : w.Constrained S n) (B : FixedBase)
    (hz : ∀ j, j < 85 → (B.params j).z + 1 ≠ 0) {o oa : ℕ}
    (ho : o + 170 ≤ n) (hoa : oa + 4 ≤ n)
    (hR : w.FixedMulRegion B o) (hsel : w.qAdd oa = 1)
    (hcp : w.pt01 oa = w.pt12 (o + 168)) (hcq : w.pt01 (oa + 1) = w.pt12 (o + 169)) :
    ∃ α : CompElliptic.Fields.Pasta.Fq, w.pt01 (oa + 2) = α • B := by
  obtain ⟨ks, hks, hlast, hacc⟩ := fixedMulRegion_sound h B hz ho hR
  refine ⟨windowsScalar ks, ?_⟩
  have hpv : (w.pt01 oa).Valid := by
    rw [hcp, hlast]
    exact Or.inl (B.windowPoint_onCurve (hks 84))
  have hqv : (w.pt01 (oa + 1)).Valid := by
    rw [hcq, hacc]
    exact Point.valid_nsmul (Or.inl B.onCurve) _
  rw [add_sound h (by omega) hsel hpv hqv, hcp, hcq, hlast, hacc,
    windowPoint_add_partialSum]

end Assignment

end AddressSignature
