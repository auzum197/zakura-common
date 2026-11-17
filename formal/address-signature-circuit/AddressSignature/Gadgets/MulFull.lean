import AddressSignature.Gadgets.Mul

/-!
# Variable-base scalar multiplication: the overflow check and the result

This file composes the regions of `Config::mul` and proves that the result is
`[ivk] P` for the canonical integer `ivk`.
-/

namespace AddressSignature

open Zcash.Circuits
open Zcash.Circuits.Ecc.Mul (chainNat tQNat)
open Zcash.Circuits.Ecc.Mul.Incomplete.DoubleAndAdd (accScalar)
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD PALLAS_BASE_CARD)

namespace Assignment

variable {w : Assignment} {S : ℕ → Point Fp} {n : ℕ}

/-- The selectors and internal copy constraints of all regions of one
variable-base scalar multiplication. -/
structure MulRegions (w : Assignment)
    (od oi ob0 ou0 oa0 ob1 ou1 oa1 ob2 ou2 oa2 ol ola os oo : ℕ) : Prop where
  /-- `[2] base`. -/
  dbl : w.qAdd od = 1
  inc : w.MulIncompleteRegion oi
  /-- The initial `y_a` of the chain is a copy of the `y` of `[2] base`. -/
  accY : w.a1 oi = w.a1 (od + 2)
  /-- The initial `x_a` of the chain is a copy of the `x` of `[2] base`. -/
  accX : w.a0 (oi + 2) = w.a0 (od + 2)
  bit0 : w.MulCompleteBit ob0 ou0 oa0
  z0 : w.a0 ob0 = w.a0 (oi + 505)
  acc0 : w.pt01 (ou0 + 1) = w.pt01 (oi + 504)
  bit1 : w.MulCompleteBit ob1 ou1 oa1
  z1 : w.a0 ob1 = w.a0 (ob0 + 1)
  acc1 : w.pt01 (ou1 + 1) = w.pt01 (oa0 + 2)
  bit2 : w.MulCompleteBit ob2 ou2 oa2
  z2 : w.a0 ob2 = w.a0 (ob1 + 1)
  acc2 : w.pt01 (ou2 + 1) = w.pt01 (oa1 + 2)
  lsb : w.MulLsb ol ola
  zl : w.a0 ol = w.a0 (ob2 + 1)
  accl : w.pt01 (ola + 1) = w.pt01 (oa2 + 2)
  /-- The 13 range-check words of `s`. -/
  sRange : w.RangeCheckRegion os 13
  overflow : w.qMulOverflow oo = 1
  ovZ0 : w.a0 oo = w.a0 (ol + 1)
  /-- `k_254` is the running sum after the first bit. -/
  ovK254 : w.a1 oo = w.a0 (oi + 5)
  ovS : w.a2 oo = w.a0 os
  /-- `z_130` is the running sum after 125 bits. -/
  ovZ130 : w.a0 (oo + 1) = w.a0 (oi + 253)
  ovSHi : w.a2 (oo + 1) = w.a0 (os + 13)

/-- The copy constraints that anchor the base of the multiplication to a point `P`:
each region that reads the base holds the coordinates of `P`. -/
structure MulBase (w : Assignment) (P : Point Fp)
    (od oi ob0 ou0 ob1 ou1 ob2 ou2 ol : ℕ) : Prop where
  dblP : w.pt01 od = P
  dblQ : w.pt01 (od + 1) = P
  incX : w.a1 (oi + 3) = P.x
  incY : w.a2 (oi + 3) = P.y
  u0 : w.a0 ou0 = P.x
  b0 : w.a1 ob0 = P.y
  u1 : w.a0 ou1 = P.x
  b1 : w.a1 ob1 = P.y
  u2 : w.a0 ou2 = P.x
  b2 : w.a1 ob2 = P.y
  lsbX : w.a1 (ol + 1) = P.x
  lsbY : w.a2 (ol + 1) = P.y

/-- All regions of one multiplication are in the usable rows. -/
structure MulFits (n od oi ob0 ou0 oa0 ob1 ou1 oa1 ob2 ou2 oa2 ol ola os oo : ℕ) : Prop where
  od : od + 4 ≤ n
  oi : oi + 506 ≤ n
  ob0 : ob0 + 2 ≤ n
  ou0 : ou0 + 4 ≤ n
  oa0 : oa0 + 4 ≤ n
  ob1 : ob1 + 2 ≤ n
  ou1 : ou1 + 4 ≤ n
  oa1 : oa1 + 4 ≤ n
  ob2 : ob2 + 2 ≤ n
  ou2 : ou2 + 4 ≤ n
  oa2 : oa2 + 4 ≤ n
  ol : ol + 2 ≤ n
  ola : ola + 4 ≤ n
  os : os + 14 ≤ n
  oo : oo + 3 ≤ n

/-- The overflow check: the 255-bit integer `K` that the running sum encodes is
`ivk + t_q` over the integers, for the canonical `ivk`. -/
theorem mulOverflow_sound (h : w.Constrained S n) {os oo : ℕ}
    (hos : os + 14 ≤ n) (hoo : oo + 3 ≤ n)
    (hsel : w.qMulOverflow oo = 1) (hRange : w.RangeCheckRegion os 13)
    (hS : w.a2 oo = w.a0 os) (hSHi : w.a2 (oo + 1) = w.a0 (os + 13))
    (bits : ℕ → Bool)
    (hz0 : w.a0 oo = (chainNat 0 bits 255 : Fp))
    (hk254 : w.a1 oo = (chainNat 0 bits 1 : Fp))
    (hz130 : w.a0 (oo + 1) = (chainNat 0 bits 125 : Fp)) :
    chainNat 0 bits 255 = (w.a1 (oo + 1)).val + tQNat := by
  have hz : ∀ {p : Fp}, p ∈ w.mulOverflowPolys oo → p = 0 := fun hp =>
    h.poly_zero (g := (w.qMulOverflow, w.mulOverflowPolys)) (by simp [gates]) (r := oo)
      (by omega) (by simp [hsel]) hp
  have o1 : w.a2 oo - (w.a1 (oo + 1) + w.a1 oo * (2 ^ 124 * 2 ^ 6)) = 0 :=
    hz (by simp [mulOverflowPolys])
  have o2 : w.a0 oo - w.a1 (oo + 1) - Ecc.tQ = 0 := hz (by simp [mulOverflowPolys])
  have o3 : w.a1 oo * (w.a0 (oo + 1) - 2 ^ 124) = 0 := hz (by simp [mulOverflowPolys])
  have o4 : w.a1 oo * w.a2 (oo + 1) = 0 := hz (by simp [mulOverflowPolys])
  have o5 : (1 - w.a1 oo) * (1 - w.a0 (oo + 1) * w.a0 (oo + 2)) * w.a2 (oo + 1) = 0 :=
    hz (by simp [mulOverflowPolys])
  obtain ⟨lo, hlo, hdec⟩ := rangeCheck_sound h (o := os) (num := 13) (by omega) hRange
  simp only [Nat.reduceMul] at hlo hdec
  rw [← hS, ← hSHi] at hdec
  push_cast at hdec
  have hk : w.a1 oo = if bits 0 then 1 else 0 := by
    rw [hk254]
    simp only [chainNat]
    split_ifs <;> simp
  have happ := Ecc.Mul.chainNat_append 0 bits 125 130
  have hoff := Ecc.Mul.chainNat_offset (chainNat 0 bits 125) (fun i => bits (125 + i)) 130
  have hRlt := Ecc.Mul.chainNat_lt 0 (fun i => bits (125 + i)) 130
  have hZlt := Ecc.Mul.chainNat_lt 0 bits 125
  have hmsb := Ecc.Mul.chainNat_msb bits 124
  have hmsblt := Ecc.Mul.chainNat_lt 0 (fun i => bits (i + 1)) 124
  simp only [Nat.zero_add, Nat.mul_one, Nat.reduceAdd] at happ hRlt hZlt hmsb hmsblt
  exact Ecc.Mul.k_canonical (alpha := w.a1 (oo + 1)) (k254 := w.a1 oo)
    (z130 := w.a0 (oo + 1)) (K := chainNat 0 bits 255) (Zhi := chainNat 0 bits 125)
    (R := chainNat 0 (fun i => bits (125 + i)) 130) (b254 := bits 0)
    hk hz130 hZlt
    (by
      intro hb
      rw [hmsb, hb]
      simp only [Bool.false_eq_true, if_false, Nat.mul_zero, Nat.zero_add]
      exact hmsblt)
    hRlt
    (by rw [happ, hoff])
    (by rw [← hz0]; linear_combination o2)
    (by
      rcases mul_eq_zero.mp o3 with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (by linear_combination h1))
    ⟨w.a2 (oo + 1), lo, hlo, by linear_combination hdec - o1,
      by
        rcases mul_eq_zero.mp o4 with h0 | h1
        · exact Or.inl h0
        · exact Or.inr h1,
      by
        rcases mul_eq_zero.mp o5 with h0 | h1
        · rcases mul_eq_zero.mp h0 with h00 | h01
          · exact Or.inl (by linear_combination -h00)
          · refine Or.inr (Or.inl ?_)
            intro hzero
            rw [hzero] at h01
            simp at h01
        · exact Or.inr (Or.inr h1)⟩

/-- `Config::mul`: the result cells hold `[ivk] P`, where `ivk` is the canonical
integer of the scalar cell `a1 (oo + 1)`. -/
theorem mul_sound (h : w.Constrained S n)
    {od oi ob0 ou0 oa0 ob1 ou1 oa1 ob2 ou2 oa2 ol ola os oo : ℕ}
    (hF : MulFits n od oi ob0 ou0 oa0 ob1 ou1 oa1 ob2 ou2 oa2 ol ola os oo)
    (hR : w.MulRegions od oi ob0 ou0 oa0 ob1 ou1 oa1 ob2 ou2 oa2 ol ola os oo)
    {P : Point Fp} (hP : P.OnCurve)
    (hB : w.MulBase P od oi ob0 ou0 ob1 ou1 ob2 ou2 ol) :
    w.pt01 (ola + 2) = (w.a1 (oo + 1)).val • P := by
  have hPv : P.Valid := Or.inl hP
  -- `[2] P`
  have hdbl : w.pt01 (od + 2) = 2 • P := by
    rw [add_sound h (r := od) (by have := hF.od; omega) hR.dbl (by rw [hB.dblP]; exact hPv)
      (by rw [hB.dblQ]; exact hPv), hB.dblP, hB.dblQ]
    exact point_two_nsmul hP
  -- the running sum before each of the 255 bits, and after the last bit
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℕ → Fp, Z = fun r =>
      if r ≤ 251 then w.a0 (oi + 2 * r + 3)
      else if r = 252 then w.a0 (ob0 + 1)
      else if r = 253 then w.a0 (ob1 + 1)
      else if r = 254 then w.a0 (ob2 + 1)
      else w.a0 (ol + 1) := ⟨_, rfl⟩
  have hZ : ∀ r, r ≤ 251 → Z r = w.a0 (oi + 2 * r + 3) := by
    intro r hr; rw [hZdef]; simp only [if_pos hr]
  have hZ251 : Z 251 = w.a0 (oi + 505) := hZ 251 le_rfl
  have hZ252 : Z 252 = w.a0 (ob0 + 1) := by rw [hZdef]; simp
  have hZ253 : Z 253 = w.a0 (ob1 + 1) := by rw [hZdef]; simp
  have hZ254 : Z 254 = w.a0 (ob2 + 1) := by rw [hZdef]; simp
  have hZ255 : Z 255 = w.a0 (ol + 1) := by rw [hZdef]; simp
  -- the incomplete chain
  obtain ⟨hZ0, hbool, hacc⟩ := mulIncomplete_sound h hF.oi hR.inc hP hB.incX hB.incY
    (by rw [hR.accX]; exact congrArg Point.x hdbl)
    (by rw [hR.accY]; exact congrArg Point.y hdbl) Z hZ
  have h2le : ∀ b, 2 ≤ accScalar 2 (zBits Z) b :=
    Ecc.Mul.Incomplete.DoubleAndAdd.accScalar_two_le (by norm_num) _
  -- the three complete bits
  obtain ⟨hb251, hacc1⟩ := mulCompleteBit_sound h hF.ob0 hF.ou0 hF.oa0 hR.bit0 hP hB.u0 hB.b0
    (A := accScalar 2 (zBits Z) 251) (by have := h2le 251; omega) (by rw [hR.acc0, hacc])
  rw [hR.z0, ← hZ251, ← hZ252] at hb251 hacc1
  obtain ⟨hb252, hacc2⟩ := mulCompleteBit_sound h hF.ob1 hF.ou1 hF.oa1 hR.bit1 hP hB.u1 hB.b1
    (A := accScalar 2 (zBits Z) 252) (by have := h2le 252; omega)
    (by rw [hR.acc1, hacc1]; rfl)
  rw [hR.z1, ← hZ252, ← hZ253] at hb252 hacc2
  obtain ⟨hb253, hacc3⟩ := mulCompleteBit_sound h hF.ob2 hF.ou2 hF.oa2 hR.bit2 hP hB.u2 hB.b2
    (A := accScalar 2 (zBits Z) 253) (by have := h2le 253; omega)
    (by rw [hR.acc2, hacc2]; rfl)
  rw [hR.z2, ← hZ253, ← hZ254] at hb253 hacc3
  -- the least significant bit
  obtain ⟨hb254, hres⟩ := mulLsb_sound h hF.ol hF.ola hR.lsb hP hB.lsbX hB.lsbY
    (M := accScalar 2 (zBits Z) 254) (by rw [hR.accl, hacc3]; rfl)
  rw [hR.zl, ← hZ254, ← hZ255] at hb254 hres
  -- the running sum is the chain of its bits
  have hboolAll : ∀ r, r < 255 → IsBool (Z (r + 1) - 2 * Z r) := by
    intro r hr
    by_cases hr250 : r ≤ 250
    · exact hbool r hr250
    · obtain rfl | rfl | rfl | rfl : r = 251 ∨ r = 252 ∨ r = 253 ∨ r = 254 := by omega
      · exact hb251
      · exact hb252
      · exact hb253
      · exact hb254
  have hchain := zBits_chain 255 hZ0 hboolAll
  -- the overflow check
  have hK := mulOverflow_sound h hF.os hF.oo hR.overflow hR.sRange hR.ovS hR.ovSHi (zBits Z)
    (by rw [hR.ovZ0, ← hZ255]; exact hchain 255 le_rfl)
    (by rw [hR.ovK254, ← hchain 1 (by norm_num)]; exact (hZ 1 (by norm_num)).symm)
    (by rw [hR.ovZ130, ← hchain 125 (by norm_num)]; exact (hZ 125 (by norm_num)).symm)
  -- the result
  have hclosed := Ecc.Mul.accScalar_closed 2 (by norm_num) (zBits Z) 254
  have hKstep : chainNat 0 (zBits Z) 255
      = 2 * chainNat 0 (zBits Z) 254 + (if zBits Z 254 then 1 else 0) := rfl
  have hcard : PALLAS_SCALAR_CARD = 2 ^ 254 + tQNat := by
    norm_num [PALLAS_SCALAR_CARD, tQNat]
  have hbit : zBits Z 254 = decide (Z 255 - 2 * Z 254 = 1) := rfl
  rw [← hbit] at hres
  have hfinal : w.pt01 (ola + 2) = (2 ^ 254 + chainNat 0 (zBits Z) 255) • P := by
    rw [hres]
    obtain ⟨M, hM⟩ : ∃ M : ℕ, M = accScalar 2 (zBits Z) 254 := ⟨_, rfl⟩
    rw [← hM] at hclosed ⊢
    cases hb : zBits Z 254
    · rw [hb] at hKstep
      simp only [Bool.false_eq_true, if_false] at hKstep ⊢
      rw [point_neg_add_nsmul hP (by omega)]
      congr 1
      omega
    · rw [hb] at hKstep
      simp only [if_true] at hKstep ⊢
      rw [point_zero_add (Point.valid_nsmul hPv M)]
      congr 1
      omega
  rw [hfinal, hK]
  apply Point.nsmul_congr hP
  show (2 ^ 254 + ((w.a1 (oo + 1)).val + tQNat)) % PALLAS_SCALAR_CARD
    = (w.a1 (oo + 1)).val % PALLAS_SCALAR_CARD
  rw [show 2 ^ 254 + ((w.a1 (oo + 1)).val + tQNat)
      = (w.a1 (oo + 1)).val + PALLAS_SCALAR_CARD by rw [hcard]; ring, Nat.add_mod_right]

end Assignment

end AddressSignature
