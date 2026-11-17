import AddressSignature.Gadgets.Sinsemilla

/-!
# `Commit^ivk`: canonicity of `ak` and `nk`, and the message of the hash

The two canonicity gates of `chip/commit_ivk.rs` tie the four hashed pieces
`a`, `b`, `c`, `d` to the canonical 255-bit encodings of `ak` and `nk`. This file
proves that the 51 words that the circuit hashes are the 51 words of
`I2LEBSP_255(ak) ‖ I2LEBSP_255(nk)`.
-/

namespace AddressSignature

open Zcash.Circuits
open Zcash.Circuits.Specs (bitrange)
open Zcash.Circuits.Specs.Sinsemilla (hashToPoint commitIvkChunks)
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)

theorem map_range_51 (ms : ℕ → ℕ) :
    (List.range 51).map ms =
      (List.range 25).map ms ++ (List.range 1).map (fun r => ms (25 + r))
        ++ (List.range 24).map (fun r => ms (26 + r))
        ++ (List.range 1).map (fun r => ms (50 + r)) := by
  have hsplit : List.range 51 =
      List.range 25 ++ (List.range 1).map (25 + ·) ++ (List.range 24).map (26 + ·)
        ++ (List.range 1).map (50 + ·) := by decide
  rw [hsplit]
  simp only [List.map_append, List.map_map]
  rfl

namespace Assignment

variable {w : Assignment} {S : ℕ → Point Fp} {n : ℕ}

/-- The cells and copy constraints of the two canonicity regions, at rows `oka` and
`okn`, with respect to the hash region `oh`, the short range checks of `b_0`, `b_2`,
`d_0` at `ob0`, `ob2`, `od0`, and the range checks of `a'` and `b2c'` at `oap`,
`obp`. -/
structure CanonicityRegions (w : Assignment) (oh ob0 ob2 od0 oap obp oka okn : ℕ) : Prop where
  selAk : w.qCommitIvkAk oka = 1
  selNk : w.qCommitIvkNk okn = 1
  /-- `a` is the first running sum of piece `a`. -/
  a : w.a1 oka = w.a0 (oh + 1)
  /-- `b` is the first running sum of piece `b` (word 25). -/
  b : w.a2 oka = w.a0 (oh + 51)
  b0 : w.a0 (oka + 1) = w.a0 ob0
  b2 : w.a2 (oka + 1) = w.a0 ob2
  /-- `z13_a` is the running sum of piece `a` at word 13. -/
  z13a : w.a0 (oka + 2) = w.a0 (oh + 27)
  aPrime : w.a1 (oka + 2) = w.a0 oap
  z13aPrime : w.a2 (oka + 2) = w.a0 (oap + 13)
  /-- `c` is the first running sum of piece `c` (word 26). -/
  c : w.a1 okn = w.a0 (oh + 53)
  /-- `d` is the first running sum of piece `d` (word 50). -/
  d : w.a2 okn = w.a0 (oh + 101)
  d0 : w.a0 (okn + 1) = w.a0 od0
  b2' : w.a2 (okn + 1) = w.a0 ob2
  /-- `z13_c` is the running sum of piece `c` at its word 13 (word 39). -/
  z13c : w.a0 (okn + 2) = w.a0 (oh + 79)
  b2cPrime : w.a1 (okn + 2) = w.a0 obp
  z14b2cPrime : w.a2 (okn + 2) = w.a0 (obp + 14)

/-- The words that the circuit hashes are the words of the canonical encodings of
`ak = a0 oka` and `nk = a0 okn`: if the Sinsemilla hash of
`I2LEBSP_255(ak) ‖ I2LEBSP_255(nk)` from `Q` is defined, the output cells of the
hash region hold it. -/
theorem commitIvk_hash_sound (h : w.Constrained S n) {Q : Point Fp}
    {oh ob0 ob2 od0 oap obp oka okn : ℕ}
    (hoh : oh + 104 ≤ n) (hob0 : ob0 + 2 ≤ n) (hob2 : ob2 + 2 ≤ n) (hod0 : od0 + 2 ≤ n)
    (hoap : oap + 14 ≤ n) (hobp : obp + 15 ≤ n) (hoka : oka + 3 ≤ n) (hokn : okn + 3 ≤ n)
    (hH : w.SinsemillaRegion Q oh)
    (hB0 : w.ShortRangeCheckRegion ob0 4) (hB2 : w.ShortRangeCheckRegion ob2 5)
    (hD0 : w.ShortRangeCheckRegion od0 9)
    (hAP : w.RangeCheckRegion oap 13) (hBP : w.RangeCheckRegion obp 14)
    (hC : w.CanonicityRegions oh ob0 ob2 od0 oap obp oka okn) :
    ∀ B, hashToPoint S Q (commitIvkChunks (w.a0 oka).val (w.a0 okn).val) = some B →
      w.pt01 (oh + 102) = B := by
  obtain ⟨ms, hms, hw⟩ := sinsemilla_words h hoh hH
  obtain ⟨pA, pZ13, pB, pC, pD⟩ := sinsemilla_pieces hH hw
  have hcard : (2 : ℕ) ^ 250 < PALLAS_BASE_CARD := by norm_num [PALLAS_BASE_CARD]
  -- the gate constraints
  have hzA : ∀ {p : Fp}, p ∈ w.commitIvkAkPolys oka → p = 0 := fun hp =>
    h.poly_zero (g := (w.qCommitIvkAk, w.commitIvkAkPolys)) (by simp [gates]) (r := oka)
      (by omega) (by simp [hC.selAk]) hp
  have hzN : ∀ {p : Fp}, p ∈ w.commitIvkNkPolys okn → p = 0 := fun hp =>
    h.poly_zero (g := (w.qCommitIvkNk, w.commitIvkNkPolys)) (by simp [gates]) (r := okn)
      (by omega) (by simp [hC.selNk]) hp
  have g1 : boolCheck (w.a1 (oka + 1)) = 0 := hzA (by simp [commitIvkAkPolys])
  have g2 : w.a2 oka - (w.a0 (oka + 1) + w.a1 (oka + 1) * 2 ^ 4 + w.a2 (oka + 1) * 2 ^ 5) = 0 :=
    hzA (by simp [commitIvkAkPolys])
  have g3 : w.a1 oka + w.a0 (oka + 1) * 2 ^ 250 + w.a1 (oka + 1) * 2 ^ 254 - w.a0 oka = 0 :=
    hzA (by simp [commitIvkAkPolys])
  have g4 : w.a1 (oka + 1) * w.a0 (oka + 1) = 0 := hzA (by simp [commitIvkAkPolys])
  have g5 : w.a1 (oka + 1) * w.a0 (oka + 2) = 0 := hzA (by simp [commitIvkAkPolys])
  have g6 : w.a1 oka + 2 ^ 130 - tP - w.a1 (oka + 2) = 0 := hzA (by simp [commitIvkAkPolys])
  have g7 : w.a1 (oka + 1) * w.a2 (oka + 2) = 0 := hzA (by simp [commitIvkAkPolys])
  have n1 : boolCheck (w.a1 (okn + 1)) = 0 := hzN (by simp [commitIvkNkPolys])
  have n2 : w.a2 okn - (w.a0 (okn + 1) + w.a1 (okn + 1) * 2 ^ 9) = 0 :=
    hzN (by simp [commitIvkNkPolys])
  have n3 : w.a2 (okn + 1) + w.a1 okn * 2 ^ 5 + w.a0 (okn + 1) * 2 ^ 245
      + w.a1 (okn + 1) * 2 ^ 254 - w.a0 okn = 0 := hzN (by simp [commitIvkNkPolys])
  have n4 : w.a1 (okn + 1) * w.a0 (okn + 1) = 0 := hzN (by simp [commitIvkNkPolys])
  have n6 : w.a2 (okn + 1) + w.a1 okn * 2 ^ 5 + 2 ^ 140 - tP - w.a1 (okn + 2) = 0 :=
    hzN (by simp [commitIvkNkPolys])
  have n7 : w.a1 (okn + 1) * w.a2 (okn + 2) = 0 := hzN (by simp [commitIvkNkPolys])
  -- piece `a`
  obtain ⟨sA, hsA⟩ : ∃ sA : ℕ, sA = ∑ j ∈ Finset.range 25, ms j * 2 ^ (10 * j) := ⟨_, rfl⟩
  have hsA_lt : sA < 2 ^ 250 := by
    have := Specs.Sinsemilla.sum_digits_lt (Kb := 10) hms 25
    rw [hsA]; simpa using this
  have ha_eq : w.a1 oka = (sA : Fp) := by rw [hC.a, pA, hsA]
  have ha_val : (w.a1 oka).val = sA := by
    rw [ha_eq, ZMod.val_natCast_of_lt (by omega)]
  have hz13A : w.a0 (oka + 2) = (((w.a1 oka).val / 2 ^ 130 : ℕ) : Fp) := by
    have hdiv := Specs.Sinsemilla.sum_suffix_div (Kb := 10) hms 25 13 (by norm_num)
    simp only [Nat.reduceMul, Nat.reduceSub] at hdiv
    rw [ha_val, hsA, hdiv, hC.z13a, pZ13]
  -- piece `c`
  obtain ⟨sC, hsC⟩ : ∃ sC : ℕ, sC = ∑ j ∈ Finset.range 24, ms (26 + j) * 2 ^ (10 * j) :=
    ⟨_, rfl⟩
  have hsC_lt : sC < 2 ^ 240 := by
    have := Specs.Sinsemilla.sum_digits_lt (Kb := 10) (d := fun j => ms (26 + j))
      (fun j => hms _) 24
    rw [hsC]; simpa using this
  have hc_eq : w.a1 okn = (sC : Fp) := by rw [hC.c, pC, hsC]
  have hc_val : (w.a1 okn).val = sC := by
    rw [hc_eq, ZMod.val_natCast_of_lt (by omega)]
  -- the short range checks
  have hb0_lt : (w.a0 (oka + 1)).val < 2 ^ 4 := by
    rw [hC.b0]; exact shortRangeCheck_sound h hob0 (by norm_num) hB0
  have hb2_lt : (w.a2 (okn + 1)).val < 2 ^ 5 := by
    rw [hC.b2']; exact shortRangeCheck_sound h hob2 (by norm_num) hB2
  have hd0_lt : (w.a0 (okn + 1)).val < 2 ^ 9 := by
    rw [hC.d0]; exact shortRangeCheck_sound h hod0 (by norm_num) hD0
  -- the range checks of `a'` and `b2c'`
  obtain ⟨loA, hloA, hdecA⟩ := rangeCheck_sound h (o := oap) (num := 13) (by omega) hAP
  obtain ⟨loB, hloB, hdecB⟩ := rangeCheck_sound h (o := obp) (num := 14) (by omega) hBP
  simp only [Nat.reduceMul] at hloA hdecA hloB hdecB
  rw [← hC.aPrime, ← hC.z13aPrime] at hdecA
  rw [← hC.b2cPrime, ← hC.z14b2cPrime] at hdecB
  -- canonicity of `ak` and `nk`
  obtain ⟨haB, hb0B, hb1B⟩ := CommitIvk.Gate.soundness_ak
    (ak := w.a0 oka) (a := w.a1 oka) (b0 := w.a0 (oka + 1)) (b1 := w.a1 (oka + 1))
    (z13A := w.a0 (oka + 2)) (aPrime := w.a1 (oka + 2)) (z13APrime := w.a2 (oka + 2))
    (by rw [ha_val]; exact hsA_lt) hb0_lt (isBool_of_boolCheck g1)
    (by push_cast; linear_combination -g6) hz13A ⟨loA, hloA, hdecA⟩
    (by push_cast; linear_combination g3) g4 g5 g7
  obtain ⟨hb2B, hcB, hd0B, hd1B⟩ := CommitIvk.Gate.soundness_nk
    (nk := w.a0 okn) (b2 := w.a2 (okn + 1)) (c := w.a1 okn) (d0 := w.a0 (okn + 1))
    (d1 := w.a1 (okn + 1)) (b2CPrime := w.a1 (okn + 2)) (z14B2CPrime := w.a2 (okn + 2))
    hb2_lt (by rw [hc_val]; exact hsC_lt) hd0_lt (isBool_of_boolCheck n1)
    (by push_cast; linear_combination -n6) ⟨loB, hloB, hdecB⟩
    (by push_cast; linear_combination n3) n4 n7
  -- the message words
  have hak : (w.a0 oka).val < 2 ^ 255 :=
    lt_trans (ZMod.val_lt _) (by norm_num [PALLAS_BASE_CARD])
  have hnk : (w.a0 okn).val < 2 ^ 255 :=
    lt_trans (ZMod.val_lt _) (by norm_num [PALLAS_BASE_CARD])
  have hmsK : ∀ r, ms r < 2 ^ Specs.K := hms
  have hchunks := CommitIvk.commitIvkChunks_eq_of_piece_digit_sums
    (msA := ms) (msB := fun r => ms (25 + r)) (msC := fun r => ms (26 + r))
    (msD := fun r => ms (50 + r)) (ak := (w.a0 oka).val) (nk := (w.a0 okn).val)
    hmsK (fun r => hmsK _) (fun r => hmsK _) (fun r => hmsK _)
    (by
      have hmod : (w.a0 oka).val % 2 ^ (Specs.K * 25) = sA := by
        rw [← ha_val, haB, Specs.bitrange_zero]; rfl
      rw [hmod, hsA]; rfl)
    (by
      rw [← hb0B, ← hb1B, ← hb2B]
      simp only [Finset.sum_range_one, Nat.add_zero, Nat.mul_zero, pow_zero, Nat.mul_one]
      push_cast
      rw [ZMod.natCast_rightInverse (w.a0 (oka + 1)),
        ZMod.natCast_rightInverse (w.a1 (oka + 1)),
        ZMod.natCast_rightInverse (w.a2 (okn + 1)), hC.b2', ← hC.b2, ← pB, ← hC.b]
      linear_combination -g2)
    (by
      have hmod : (w.a0 okn).val / 2 ^ 5 % 2 ^ (Specs.K * 24) = sC := by
        rw [← hc_val, hcB]; rfl
      rw [hmod, hsC]; rfl)
    (by
      rw [← hd0B, ← hd1B]
      simp only [Finset.sum_range_one, Nat.add_zero, Nat.mul_zero, pow_zero, Nat.mul_one]
      push_cast
      rw [ZMod.natCast_rightInverse (w.a0 (okn + 1)),
        ZMod.natCast_rightInverse (w.a1 (okn + 1)), ← pD, ← hC.d]
      linear_combination -n2)
    hak hnk
  rw [← hchunks, ← map_range_51]
  exact sinsemilla_chain h hoh hH hw

end Assignment

end AddressSignature
