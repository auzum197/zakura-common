import AddressSignature.Gadgets.Add

/-!
# The merged lookup, and range checks through the generator table

The circuit has one lookup argument. Its three input expressions depend on the
ternary fixed column `f_lookup` (shortcut 2):

* `f_lookup = 1` (Sinsemilla word): `(word, x_p, y_p)`;
* `f_lookup = 2` (range-check row): `(word, a1, a2)` with `a1`, `a2` witnessed;
* `f_lookup = 0`: `(0, x(S_0), y(S_0))`.

The table has one row for each 10-bit index. A range-check row that passes the
lookup thus has a word below `2^10`, whatever the prover puts in `a1` and `a2`.
-/

namespace AddressSignature

open Zcash.Circuits
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)

namespace Assignment

variable {w : Assignment} {S : ℕ → Point Fp} {n : ℕ}

theorem two_mul_twoInv : (2 : Fp) * twoInv = 1 :=
  mul_inv_cancel₀ Zcash.Circuits.two_ne_zero

/-- On a row with `f_lookup = 1`, the indicators are `(f_sin, f_rc) = (1, 0)`. -/
theorem fSin_fRc_of_one {r : ℕ} (hf : w.fLookup r = 1) : w.fSin r = 1 ∧ w.fRc r = 0 := by
  constructor
  · simp only [fSin, hf]; norm_num
  · simp only [fRc, hf]; norm_num

/-- On a row with `f_lookup = 2`, the indicators are `(f_sin, f_rc) = (0, 1)`. -/
theorem fSin_fRc_of_two {r : ℕ} (hf : w.fLookup r = 2) : w.fSin r = 0 ∧ w.fRc r = 1 := by
  constructor
  · simp only [fSin, hf]; norm_num
  · simp only [fRc, hf]
    have := two_mul_twoInv
    linear_combination this

theorem qRun_of_one {r : ℕ} (hs : w.fS2 r = 1) : w.qRun r = 1 := by
  simp only [qRun, qS3, hs]; norm_num

theorem qRun_of_zero {r : ℕ} (hs : w.fS2 r = 0) : w.qRun r = 0 := by
  simp only [qRun, qS3, hs]; norm_num

theorem qRun_of_two {r : ℕ} (hs : w.fS2 r = 2) : w.qRun r = 0 := by
  simp only [qRun, qS3, hs]; norm_num

/-- The lookup on a range-check row: the word is below `2^10`. -/
theorem lookup_rangeCheck (h : w.Constrained S n) {r : ℕ} (hr : r < n)
    (hf : w.fLookup r = 2) :
    ∃ i : ℕ, i < 2 ^ 10 ∧ w.a0 r - w.qRun r * w.a0 (r + 1) * 2 ^ 10 = (i : Fp) := by
  obtain ⟨i, hi, hidx, -, -⟩ := h.lookup r hr
  obtain ⟨hs, hc⟩ := fSin_fRc_of_two hf
  refine ⟨i, hi, ?_⟩
  rw [← hidx]
  simp only [lookupIndex, hs, hc]
  ring

/-- The lookup on a Sinsemilla word: the word is below `2^10`, and `(x_p, y_p)` is
the generator of the word. -/
theorem lookup_sinsemilla (h : w.Constrained S n) {r : ℕ} (hr : r < n)
    (hf : w.fLookup r = 1) :
    ∃ i : ℕ, i < 2 ^ 10 ∧
      w.a0 (r + 1) - w.qRun r * w.a0 (r + 3) * 2 ^ 10 = (i : Fp) ∧
      w.a1 (r + 1) = (S i).x ∧ w.sinYP r = (S i).y := by
  obtain ⟨i, hi, hidx, hx, hy⟩ := h.lookup r hr
  obtain ⟨hs, hc⟩ := fSin_fRc_of_one hf
  refine ⟨i, hi, ?_, ?_, ?_⟩
  · rw [← hidx]
    simp only [lookupIndex, hs, hc]
    ring
  · rw [← hx]
    simp only [lookupX, hs, hc]
    ring
  · rw [← hy]
    simp only [lookupY, hs, hc]
    ring

/-! ## Running-sum range check -/

/-- The fixed cells of a region "range check" of `num` words at row `o`: each word
row is a range-check row in running-sum mode. -/
structure RangeCheckRegion (w : Assignment) (o num : ℕ) : Prop where
  lookup : ∀ i, i < num → w.fLookup (o + i) = 2
  mode : ∀ i, i < num → w.fS2 (o + i) = 1

/-- `Config::range_check`: the value in row `o` is a `10 * num`-bit integer plus
`2^(10 * num)` times the last running sum in row `o + num`. -/
theorem rangeCheck_sound (h : w.Constrained S n) {o num : ℕ} (ho : o + num ≤ n)
    (hR : w.RangeCheckRegion o num) :
    ∃ lo : ℕ, lo < 2 ^ (10 * num) ∧
      w.a0 o = (lo : Fp) + ((2 ^ (10 * num) : ℕ) : Fp) * w.a0 (o + num) := by
  have := Specs.Sinsemilla.running_sum_telescope 10 (fun i => w.a0 (o + i)) num (by
    intro i hi
    obtain ⟨wd, hwd, hword⟩ := lookup_rangeCheck h (r := o + i) (by omega) (hR.lookup i hi)
    rw [qRun_of_one (hR.mode i hi)] at hword
    refine ⟨wd, hwd, ?_⟩
    show w.a0 (o + i) = (wd : Fp) + ((2 ^ 10 : ℕ) : Fp) * w.a0 (o + i + 1)
    push_cast
    linear_combination hword)
  simpa using this

/-! ## Short range check -/

/-- The fixed cells of a region "short range check" of `bits` bits at row `o`. -/
structure ShortRangeCheckRegion (w : Assignment) (o bits : ℕ) : Prop where
  shift : w.qShift o = 1
  /-- The shift factor `2^(10 - bits)`, in `lagrange[0]` (shortcut 3). -/
  factor : w.lagrange 0 o = 2 ^ (10 - bits)
  lookup0 : w.fLookup o = 2
  mode0 : w.fS2 o = 0
  lookup1 : w.fLookup (o + 1) = 2
  mode1 : w.fS2 (o + 1) = 0

/-- `Config::range_check_short`: the value in row `o` is below `2^bits`. -/
theorem shortRangeCheck_sound (h : w.Constrained S n) {o bits : ℕ} (ho : o + 2 ≤ n)
    (hb : bits ≤ 10) (hR : w.ShortRangeCheckRegion o bits) :
    (w.a0 o).val < 2 ^ bits := by
  obtain ⟨i, hi, hword⟩ := lookup_rangeCheck h (r := o) (by omega) hR.lookup0
  obtain ⟨i', hi', hword'⟩ := lookup_rangeCheck h (r := o + 1) (by omega) hR.lookup1
  rw [qRun_of_zero hR.mode0] at hword
  rw [qRun_of_zero hR.mode1] at hword'
  have hv : w.a0 o = (i : Fp) := by linear_combination hword
  have hv' : w.a0 (o + 1) = (i' : Fp) := by linear_combination hword'
  have hshift : w.a0 o * w.lagrange 0 o - w.a0 (o + 1) = 0 :=
    h.poly_zero (g := (w.qShift, w.shiftPolys)) (by simp [gates]) (r := o) (by omega)
      (by simp [hR.shift]) (by simp [shiftPolys])
  rw [hR.factor, hv, hv'] at hshift
  have hcast : ((i * 2 ^ (10 - bits) : ℕ) : Fp) = ((i' : ℕ) : Fp) := by
    push_cast
    linear_combination hshift
  have hpow : 2 ^ (10 - bits) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hprod : i * 2 ^ (10 - bits) < 2 ^ 20 := by
    calc i * 2 ^ (10 - bits) < 2 ^ 10 * 2 ^ 10 :=
          Nat.mul_lt_mul_of_lt_of_le hi hpow (by norm_num)
      _ = 2 ^ 20 := by norm_num
  have hcard : 2 ^ 20 < PALLAS_BASE_CARD := by norm_num [PALLAS_BASE_CARD]
  have hnat : i * 2 ^ (10 - bits) = i' := by
    have := congrArg ZMod.val hcast
    rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at this
  have hsplit : 2 ^ bits * 2 ^ (10 - bits) = 2 ^ 10 := by
    rw [← pow_add]; congr 1; omega
  have hlt : i < 2 ^ bits := by
    by_contra hge
    push Not at hge
    have : 2 ^ bits * 2 ^ (10 - bits) ≤ i * 2 ^ (10 - bits) := Nat.mul_le_mul_right _ hge
    omega
  rw [hv, ZMod.val_natCast_of_lt (by omega)]
  exact hlt

end Assignment

end AddressSignature
