import AddressSignature.Gates

/-!
# Gate extraction, the non-identity point gate, and complete addition
-/

namespace AddressSignature

open Zcash.Circuits

namespace Assignment

variable {w : Assignment} {S : ℕ → Point Fp} {n : ℕ}

/-- If a gate's selector is not zero on a usable row, each of its constraint
polynomials is zero on that row. -/
theorem Constrained.poly_zero (h : w.Constrained S n)
    {g : (ℕ → Fp) × (ℕ → List Fp)} (hg : g ∈ w.gates) {r : ℕ} (hr : r < n)
    (hsel : g.1 r ≠ 0) {p : Fp} (hp : p ∈ g.2 r) : p = 0 := by
  have := h.gates g hg r hr p hp
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 hsel
  · exact h0

/-- The point in columns `a0`, `a1` of row `r`. -/
def pt01 (w : Assignment) (r : ℕ) : Point Fp := ⟨w.a0 r, w.a1 r⟩

/-- The point in columns `a1`, `a2` of row `r`. -/
def pt12 (w : Assignment) (r : ℕ) : Point Fp := ⟨w.a1 r, w.a2 r⟩

/-- Gate "witness non-identity point": the cells are a point on the curve. -/
theorem point_sound (h : w.Constrained S n) {r : ℕ} (hr : r < n)
    (hsel : w.qPoint r = 1) : (w.pt01 r).OnCurve := by
  have hp := h.poly_zero (g := (w.qPoint, w.pointPolys)) (by simp [gates]) hr
    (by simp [hsel]) (p := w.a1 r * w.a1 r - w.a0 r * w.a0 r * w.a0 r - pallasB)
    (by simp [pointPolys])
  show w.a1 r ^ 2 = w.a0 r ^ 3 + pallasB
  linear_combination hp

end Assignment

theorem isBool_of_boolCheck {v : Fp} (h : Assignment.boolCheck v = 0) : IsBool v := by
  unfold Assignment.boolCheck at h
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linear_combination -h1)

/-- The twelve constraints of complete addition imply the group law. -/
theorem add_of_polys {xp yp xq yq xr yr lam al be ga de : Fp}
    (hp : (⟨xp, yp⟩ : Point Fp).Valid) (hq : (⟨xq, yq⟩ : Point Fp).Valid)
    (h1 : (xq - xp) * ((xq - xp) * lam - (yq - yp)) = 0)
    (h2 : (1 - (xq - xp) * al) * (2 * yp * lam - 3 * (xp * xp)) = 0)
    (h3a : xp * xq * (xq - xp) * (lam * lam - xp - xq - xr) = 0)
    (h3b : xp * xq * (xq - xp) * (lam * (xp - xr) - yp - yr) = 0)
    (h3c : xp * xq * (yq + yp) * (lam * lam - xp - xq - xr) = 0)
    (h3d : xp * xq * (yq + yp) * (lam * (xp - xr) - yp - yr) = 0)
    (h4a : (1 - xp * be) * (xr - xq) = 0)
    (h4b : (1 - xp * be) * (yr - yq) = 0)
    (h5a : (1 - xq * ga) * (xr - xp) = 0)
    (h5b : (1 - xq * ga) * (yr - yp) = 0)
    (h6a : (1 - (xq - xp) * al - (yq + yp) * de) * xr = 0)
    (h6b : (1 - (xq - xp) * al - (yq + yp) * de) * yr = 0) :
    (⟨xr, yr⟩ : Point Fp) = ⟨xp, yp⟩ + ⟨xq, yq⟩ := by
  have key := Ecc.Add.add_of_spec
    (row := { x_p := xp, y_p := yp, x_qr := ⟨xq, xr⟩, y_qr := ⟨yq, yr⟩,
              lambda := lam, alpha := al, beta := be, gamma := ga, delta := de })
    hp hq ?_
  · exact key
  · simp only [Ecc.Add.Gate.Spec, Ecc.Add.Gate.Input.p, Ecc.Add.Gate.Input.q,
      Ecc.Add.Gate.Input.r]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hne
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hne
      · linear_combination h
    · intro hne
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd (by linear_combination -h) hne
      · linear_combination h
    · intro hne
      rcases mul_eq_zero.mp h3a with h | h
      · exact absurd h hne
      · rcases mul_eq_zero.mp h3b with h' | h'
        · exact absurd h' hne
        · exact ⟨by linear_combination -h, by linear_combination -h'⟩
    · intro hne
      rcases mul_eq_zero.mp h3c with h | h
      · exact absurd h hne
      · rcases mul_eq_zero.mp h3d with h' | h'
        · exact absurd h' hne
        · exact ⟨by linear_combination -h, by linear_combination -h'⟩
    · intro hne
      rcases mul_eq_zero.mp h4a with h | h
      · exact absurd (by linear_combination -h) hne
      · rcases mul_eq_zero.mp h4b with h' | h'
        · exact absurd (by linear_combination -h') hne
        · rw [Point.mk.injEq]
          exact ⟨by linear_combination h, by linear_combination h'⟩
    · intro hne
      rcases mul_eq_zero.mp h5a with h | h
      · exact absurd (by linear_combination -h) hne
      · rcases mul_eq_zero.mp h5b with h' | h'
        · exact absurd (by linear_combination -h') hne
        · rw [Point.mk.injEq]
          exact ⟨by linear_combination h, by linear_combination h'⟩
    · intro hne
      rcases mul_eq_zero.mp h6a with h | h
      · exact absurd (by linear_combination -h) hne
      · rcases mul_eq_zero.mp h6b with h' | h'
        · exact absurd (by linear_combination -h') hne
        · exact ⟨h, h'⟩

namespace Assignment

variable {w : Assignment} {S : ℕ → Point Fp} {n : ℕ}

/-- Gate "complete addition": with valid inputs in rows `r` and `r + 1`, the point in
row `r + 2` is their sum. -/
theorem add_sound (h : w.Constrained S n) {r : ℕ} (hr : r < n)
    (hsel : w.qAdd r = 1)
    (hp : (w.pt01 r).Valid) (hq : (w.pt01 (r + 1)).Valid) :
    w.pt01 (r + 2) = w.pt01 r + w.pt01 (r + 1) := by
  have hz : ∀ {p : Fp}, p ∈ w.addPolys r → p = 0 := fun hp =>
    h.poly_zero (g := (w.qAdd, w.addPolys)) (by simp [gates]) hr (by simp [hsel]) hp
  exact add_of_polys (lam := w.a2 r) (al := w.a2 (r + 1)) (be := w.a2 (r + 2))
    (ga := w.a0 (r + 3)) (de := w.a1 (r + 3)) hp hq
    (hz (by simp [addPolys])) (hz (by simp [addPolys])) (hz (by simp [addPolys]))
    (hz (by simp [addPolys])) (hz (by simp [addPolys])) (hz (by simp [addPolys]))
    (hz (by simp [addPolys])) (hz (by simp [addPolys])) (hz (by simp [addPolys]))
    (hz (by simp [addPolys])) (hz (by simp [addPolys])) (hz (by simp [addPolys]))

/-- The output of complete addition is a valid point. -/
theorem add_valid (h : w.Constrained S n) {r : ℕ} (hr : r < n)
    (hsel : w.qAdd r = 1)
    (hp : (w.pt01 r).Valid) (hq : (w.pt01 (r + 1)).Valid) :
    (w.pt01 (r + 2)).Valid := by
  rw [add_sound h hr hsel hp hq]
  exact Point.valid_add hp hq

end Assignment

end AddressSignature
