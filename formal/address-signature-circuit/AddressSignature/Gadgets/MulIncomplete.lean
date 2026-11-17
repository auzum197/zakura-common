import AddressSignature.Gadgets.Lookup

/-!
# Variable-base scalar multiplication: the incomplete chain

`Config::mul` of `chip/ecc.rs` runs the 251 incomplete double-and-add steps for the
bits `k_254 … k_4` as one chain. Step `r` (`0 ≤ r ≤ 250`) is on rows
`oi + 2 (r + 1)` and `oi + 2 (r + 1) + 1`:

```
| x_a    | lambda_1 | lambda_2 |    row oi + 2 (r + 1)
| z_prev | x_p      | y_p      |    row oi + 2 (r + 1) + 1
```

Row `oi` is the initial row. Rows `oi + 504` and `oi + 505` hold the final
accumulator and the running sum after the last bit.
-/

namespace AddressSignature

open Zcash.Circuits
open Zcash.Circuits.Ecc.Mul (chainNat)
open Zcash.Circuits.Ecc.Mul.Incomplete.DoubleAndAdd (accScalar)

/-- The bits of a running sum `Z`: bit `r` is 1 if `Z (r + 1) - 2 Z r = 1`. -/
def zBits (Z : ℕ → Fp) : ℕ → Bool := fun r => decide (Z (r + 1) - 2 * Z r = 1)

theorem zBits_step {Z : ℕ → Fp} {r : ℕ} (hb : IsBool (Z (r + 1) - 2 * Z r)) :
    Z (r + 1) - 2 * Z r = if zBits Z r then 1 else 0 := by
  unfold zBits
  rcases hb with h0 | h1
  · have hne : ¬ (Z (r + 1) - 2 * Z r = 1) := by rw [h0]; exact zero_ne_one
    simp [h0]
  · simp [h1]

/-- A running sum that starts at zero and has boolean steps is the cast of the
natural-number chain of its bits. -/
theorem zBits_chain {Z : ℕ → Fp} (N : ℕ) (h0 : Z 0 = 0)
    (hb : ∀ r, r < N → IsBool (Z (r + 1) - 2 * Z r)) :
    ∀ r, r ≤ N → Z r = (chainNat 0 (zBits Z) r : Fp) := by
  intro r
  induction r with
  | zero => intro _; simp [chainNat, h0]
  | succ r ih =>
    intro hr
    have hstep := zBits_step (hb r (by omega))
    have hprev := ih (by omega)
    simp only [chainNat]
    push_cast
    rw [← hprev]
    split_ifs with hbit
    · rw [if_pos hbit] at hstep; linear_combination hstep
    · rw [if_neg hbit] at hstep; linear_combination hstep

namespace Assignment

variable {w : Assignment} {S : ℕ → Point Fp} {n : ℕ}

/-- The four constraints of one step of the incomplete chain, in the shape that the
chain induction uses. `yn` is the `y`-coordinate of the accumulator after the step. -/
theorem mulLoop_facts {ρ : ℕ} {yn : Fp} (hz : ∀ p ∈ w.mulLoopPolys ρ yn, p = 0) :
    IsBool (w.a0 (ρ + 3) - 2 * w.a0 (ρ + 1)) ∧
    (∀ b : Bool, w.a0 (ρ + 3) - 2 * w.a0 (ρ + 1) = (if b then 1 else 0) →
      2 * w.a1 ρ * (w.a0 ρ - w.a1 (ρ + 1))
        + 2 * (((if b then 1 else 0) * 2 - 1) * w.a2 (ρ + 1)) = w.bigYA ρ) ∧
    w.a2 ρ * w.a2 ρ
      = w.a0 (ρ + 2) + (w.a1 ρ * w.a1 ρ - w.a0 ρ - w.a1 (ρ + 1)) + w.a0 ρ ∧
    2 * w.a2 ρ * (w.a0 ρ - w.a0 (ρ + 2)) = w.bigYA ρ + 2 * yn := by
  have t := two_mul_twoInv
  have g0 : boolCheck (w.a0 (ρ + 3) - w.a0 (ρ + 1) * 2) = 0 := hz _ (by simp [mulLoopPolys])
  have g1 : w.a1 ρ * (w.a0 ρ - w.a1 (ρ + 1)) - w.yA ρ
      + ((w.a0 (ρ + 3) - w.a0 (ρ + 1) * 2) * 2 - 1) * w.a2 (ρ + 1) = 0 :=
    hz _ (by simp [mulLoopPolys])
  have g2 : w.a2 ρ * w.a2 ρ - w.a0 (ρ + 2) - w.xR ρ - w.a0 ρ = 0 :=
    hz _ (by simp [mulLoopPolys])
  have g3 : w.a2 ρ * (w.a0 ρ - w.a0 (ρ + 2)) - w.yA ρ - yn = 0 :=
    hz _ (by simp [mulLoopPolys])
  unfold yA at g1 g3
  unfold xR at g2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases mul_eq_zero.mp g0 with h0 | h1
    · exact Or.inl (by linear_combination h0)
    · exact Or.inr (by linear_combination -h1)
  · intro b hk
    linear_combination 2 * g1 - 4 * w.a2 (ρ + 1) * hk + w.bigYA ρ * t
  · linear_combination g2
  · linear_combination 2 * g3 + w.bigYA ρ * t

/-- The selectors of the region "variable-base mul (incomplete addition)" at row
`oi`. -/
structure MulIncompleteRegion (w : Assignment) (oi : ℕ) : Prop where
  mul1 : w.qMul1 oi = 1
  mul2 : ∀ r, r < 250 → w.qMul2 (oi + 2 * (r + 1)) = 1
  mul3 : w.qMul3 (oi + 2 * (250 + 1)) = 1

/-- The incomplete chain. The base cells of step 0 hold `P`, the initial accumulator
is `[2] P`, and `Z r` is the running sum before bit `r`. Then the running sum starts
at zero, its 251 steps are boolean, and the final accumulator is the multiple of
`P` that the bits select. -/
theorem mulIncomplete_sound (h : w.Constrained S n) {oi : ℕ} (hoi : oi + 506 ≤ n)
    (hR : w.MulIncompleteRegion oi) {P : Point Fp} (hP : P.OnCurve)
    (hbx : w.a1 (oi + 3) = P.x) (hby : w.a2 (oi + 3) = P.y)
    (hax : w.a0 (oi + 2) = (2 • P).x) (hay : w.a1 oi = (2 • P).y)
    (Z : ℕ → Fp) (hZ : ∀ r, r ≤ 251 → Z r = w.a0 (oi + 2 * r + 3)) :
    Z 0 = 0 ∧ (∀ r, r ≤ 250 → IsBool (Z (r + 1) - 2 * Z r)) ∧
      w.pt01 (oi + 504) = accScalar 2 (zBits Z) 251 • P := by
  have t := two_mul_twoInv
  -- the initial row
  have hz1 : ∀ {p : Fp}, p ∈ w.mul1Polys oi → p = 0 := fun hp =>
    h.poly_zero (g := (w.qMul1, w.mul1Polys)) (by simp [gates]) (r := oi) (by omega)
      (by simp [hR.mul1]) hp
  have i1 : w.a1 oi - w.yA (oi + 2) = 0 := hz1 (by simp [mul1Polys])
  have i2 : w.a0 (oi + 3) = 0 := hz1 (by simp [mul1Polys])
  unfold yA at i1
  have hZ0 : Z 0 = 0 := by rw [hZ 0 (by norm_num)]; exact i2
  -- the constraints of each step
  have hloop : ∀ r, r ≤ 250 → ∀ p ∈ w.mulLoopPolys (oi + 2 * (r + 1))
      (if r < 250 then w.yA (oi + 2 * (r + 1) + 2) else w.a1 (oi + 2 * (r + 1) + 2)), p = 0 := by
    intro r hr p hp
    by_cases hlt : r < 250
    · rw [if_pos hlt] at hp
      exact h.poly_zero (g := (w.qMul2, w.mul2Polys)) (by simp [gates])
        (r := oi + 2 * (r + 1)) (by omega) (by simp [hR.mul2 r hlt])
        (by simp only [mul2Polys]; exact List.mem_append_right _ hp)
    · have hr250 : r = 250 := by omega
      subst hr250
      rw [if_neg hlt] at hp
      exact h.poly_zero (g := (w.qMul3, w.mul3Polys)) (by simp [gates])
        (r := oi + 2 * (250 + 1)) (by omega) (by simp [hR.mul3]) hp
  have hbase : ∀ r, r < 250 →
      w.a1 (oi + 2 * (r + 1) + 1) = w.a1 (oi + 2 * (r + 1) + 3) ∧
      w.a2 (oi + 2 * (r + 1) + 1) = w.a2 (oi + 2 * (r + 1) + 3) := by
    intro r hr
    have hz2 : ∀ {p : Fp}, p ∈ w.mul2Polys (oi + 2 * (r + 1)) → p = 0 := fun hp =>
      h.poly_zero (g := (w.qMul2, w.mul2Polys)) (by simp [gates])
        (r := oi + 2 * (r + 1)) (by omega) (by simp [hR.mul2 r hr]) hp
    exact ⟨sub_eq_zero.mp (hz2 (by simp [mul2Polys])),
      sub_eq_zero.mp (hz2 (by simp [mul2Polys]))⟩
  have hidx1 : ∀ r, oi + 2 * (r + 1) + 1 = oi + 2 * r + 3 := by intro r; ring
  have hidx2 : ∀ r, oi + 2 * (r + 1) + 2 = oi + 2 * (r + 1 + 1) := by intro r; ring
  have hidx3 : ∀ r, oi + 2 * (r + 1) + 3 = oi + 2 * (r + 1 + 1) + 1 := by intro r; ring
  -- the base of each step is `P`
  have hxp : ∀ r, r ≤ 250 → w.a1 (oi + 2 * (r + 1) + 1) = P.x ∧
      w.a2 (oi + 2 * (r + 1) + 1) = P.y := by
    intro r
    induction r with
    | zero => intro _; exact ⟨hbx, hby⟩
    | succ r ih =>
      intro hr
      obtain ⟨hx, hy⟩ := ih (by omega)
      obtain ⟨cx, cy⟩ := hbase r (by omega)
      rw [hidx3] at cx cy
      exact ⟨cx ▸ hx, cy ▸ hy⟩
  -- the steps are boolean
  have hbool : ∀ r, r ≤ 250 → IsBool (Z (r + 1) - 2 * Z r) := by
    intro r hr
    have := (mulLoop_facts (hloop r hr)).1
    rw [hidx1] at this
    rw [hZ (r + 1) (by omega), hZ r (by omega)]
    exact this
  refine ⟨hZ0, hbool, ?_⟩
  have haux := Ecc.Mul.Incomplete.DoubleAndAdd.soundness_aux 250 P hP 2 (by norm_num)
    (by norm_num)
    (fun r => w.a0 (oi + 2 * (r + 1)))
    (fun r => w.a1 (oi + 2 * (r + 1) + 1))
    (fun r => w.a2 (oi + 2 * (r + 1) + 1))
    (fun r => w.a1 (oi + 2 * (r + 1)))
    (fun r => w.a2 (oi + 2 * (r + 1)))
    (fun r => if r ≤ 250 then w.bigYA (oi + 2 * (r + 1)) else 2 * w.a1 (oi + 504))
    (zBits Z)
    hax
    (by
      show (if (0 : ℕ) ≤ 250 then w.bigYA (oi + 2 * (0 + 1)) else _) = _
      rw [if_pos (by norm_num), ← hay]
      show w.bigYA (oi + 2) = _
      linear_combination -2 * i1 - w.bigYA (oi + 2) * t)
    (by intro r hr; simp only [if_pos hr]; rfl)
    (fun r hr => (hxp r hr).1)
    (fun r hr => (hxp r hr).2)
    (by
      intro r hr
      simp only [if_pos hr]
      have hstep := zBits_step (hbool r hr)
      rw [hZ (r + 1) (by omega), hZ r (by omega), ← hidx1] at hstep
      exact (mulLoop_facts (hloop r hr)).2.1 (zBits Z r) hstep)
    (by
      intro r hr
      have := (mulLoop_facts (hloop r hr)).2.2.1
      rw [hidx2] at this
      exact this)
    (by
      intro r hr
      have hg := (mulLoop_facts (hloop r hr)).2.2.2
      simp only [if_pos hr]
      by_cases hlt : r < 250
      · rw [if_pos hlt, hidx2] at hg
        rw [if_pos (by omega : r + 1 ≤ 250)]
        unfold yA at hg
        linear_combination hg + w.bigYA (oi + 2 * (r + 1 + 1)) * t
      · have hr250 : r = 250 := by omega
        subst hr250
        rw [if_neg hlt] at hg
        rw [if_neg (by norm_num : ¬ (250 + 1 ≤ 250))]
        exact hg)
  obtain ⟨hx, hy⟩ := haux
  simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceLeDiff, if_false] at hx hy
  show (⟨w.a0 (oi + 504), w.a1 (oi + 504)⟩ : Point Fp) = _
  rw [Point.mk.injEq]
  exact ⟨hx, mul_left_cancel₀ Zcash.Circuits.two_ne_zero hy⟩

end Assignment

end AddressSignature
