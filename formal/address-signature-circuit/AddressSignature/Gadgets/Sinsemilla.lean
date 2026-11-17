import AddressSignature.Gadgets.Lookup

/-!
# The Sinsemilla hash of `ak ‖ nk`

`Config::hash_to_point` of `chip/sinsemilla.rs`, for the four pieces `a` (25 words),
`b` (1), `c` (24), `d` (1). Word `j` is on rows `o + 2 j` and `o + 2 j + 1`:

```
| x_a  | lambda_1  | lambda_2  |    row o + 2 j
| z    | x_p       |           |    row o + 2 j + 1
```

The output point is on row `o + 102`.
-/

namespace AddressSignature

open Zcash.Circuits
open Zcash.Circuits.Specs.Sinsemilla (hashToPoint step)

/-- One double-and-add step, from the constraints of a Sinsemilla word. `YB` is
twice the `y`-coordinate of the next accumulator. -/
theorem sin_step {A B Sm : Point Fp} (hstep : Point.doubleAndAdd A Sm = some B)
    {xa l1 l2 xp xB YB : Fp}
    (hxa : xa = A.x)
    (hYA : (l1 + l2) * (xa - (l1 * l1 - xa - xp)) = 2 * A.y)
    (hxp : xp = Sm.x)
    (hyp : (l1 + l2) * (xa - (l1 * l1 - xa - xp)) * Assignment.twoInv - l1 * (xa - xp) = Sm.y)
    (hsec : l2 * l2 - (xB + (l1 * l1 - xa - xp) + xa) = 0)
    (hY : l2 * 4 * (xa - xB) - ((l1 + l2) * (xa - (l1 * l1 - xa - xp)) * 2 + 2 * YB) = 0) :
    xB = B.x ∧ YB = 2 * B.y := by
  subst hxa
  have t := Assignment.two_mul_twoInv
  exact Ecc.DoubleAndAdd.coordinates_of_constraints hstep (xp := xp) (lambda1 := l1)
    (lambda2 := l2)
    (by linear_combination 2 * hyp - (2 * Assignment.twoInv) * hYA - (2 * A.y) * t)
    hxp hYA.symm (by linear_combination hsec) (by linear_combination hY + 2 * hYA)

/-- A piece of a running sum: if `z i = d i + 2^10 z (i + 1)` inside the piece and the
last `z` is the last word, then each `z i` is the sum of the words from `i`. -/
theorem piece_sum (z : ℕ → Fp) (d : ℕ → ℕ) (len : ℕ)
    (hrun : ∀ i, i + 1 < len → z i = (d i : Fp) + 2 ^ 10 * z (i + 1))
    (hlast : z (len - 1) = (d (len - 1) : Fp)) :
    ∀ k i, i + k + 1 = len →
      z i = ((∑ j ∈ Finset.range (k + 1), d (i + j) * 2 ^ (10 * j) : ℕ) : Fp) := by
  intro k
  induction k with
  | zero =>
    intro i hi
    have : len - 1 = i := by omega
    rw [this] at hlast
    simp [hlast]
  | succ k ih =>
    intro i hi
    have hnext := ih (i + 1) (by omega)
    have e : ∀ j, i + 1 + j = i + (j + 1) := by intro j; omega
    simp only [e] at hnext
    rw [hrun i (by omega), hnext,
      Specs.Sinsemilla.sum_head_shift 10 (k + 1) (fun j => d (i + j))]
    push_cast
    simp only [Nat.add_zero]
    norm_num

namespace Assignment

variable {w : Assignment} {S : ℕ → Point Fp} {n : ℕ}

/-- The running-sum mode `f_s2` of word `j` of the hash of `ak ‖ nk`: 0 on the last
word of pieces `a`, `b`, `c` (words 24, 25, 49), 2 on the last word of piece `d`
(word 50), and 1 on all other words. -/
def sinMode (j : ℕ) : Fp :=
  if j = 24 ∨ j = 25 ∨ j = 49 then 0 else if j = 50 then 2 else 1

/-- The fixed cells of the region "Sinsemilla hash" at row `o`, with the initial
point `Q`. -/
structure SinsemillaRegion (w : Assignment) (Q : Point Fp) (o : ℕ) : Prop where
  init : w.qSinInit o = 1
  /-- `x_Q` in `lagrange[0]` on the first row (shortcut 3). -/
  xQ : w.lagrange 0 o = Q.x
  /-- `y_Q` in `lagrange[1]` on the first row (shortcut 3). -/
  yQ : w.lagrange 1 o = Q.y
  lookup : ∀ j, j < 51 → w.fLookup (o + 2 * j) = 1
  /-- `f_s2` in `lagrange[2]` on the first row of each word (shortcut 3). -/
  mode : ∀ j, j < 51 → w.fS2 (o + 2 * j) = sinMode j

/-- The lookup facts of the 51 words `ms` of a hash region at row `o`. -/
def SinWords (w : Assignment) (S : ℕ → Point Fp) (o : ℕ) (ms : ℕ → ℕ) : Prop :=
  ∀ j, j < 51 →
    w.a0 (o + 2 * j + 1) - w.qRun (o + 2 * j) * w.a0 (o + 2 * j + 3) * 2 ^ 10 = (ms j : Fp) ∧
    w.a1 (o + 2 * j + 1) = (S (ms j)).x ∧
    w.sinYP (o + 2 * j) = (S (ms j)).y

/-- The lookup gives each word of the hash a 10-bit value and its generator. -/
theorem sinsemilla_words (h : w.Constrained S n) {Q : Point Fp} {o : ℕ}
    (ho : o + 104 ≤ n) (hR : w.SinsemillaRegion Q o) :
    ∃ ms : ℕ → ℕ, (∀ j, ms j < 2 ^ 10) ∧ w.SinWords S o ms := by
  have hall : ∀ j, ∃ m : ℕ, m < 2 ^ 10 ∧ (j < 51 →
      w.a0 (o + 2 * j + 1) - w.qRun (o + 2 * j) * w.a0 (o + 2 * j + 3) * 2 ^ 10 = (m : Fp) ∧
      w.a1 (o + 2 * j + 1) = (S m).x ∧ w.sinYP (o + 2 * j) = (S m).y) := by
    intro j
    by_cases hj : j < 51
    · obtain ⟨m, hm, hfacts⟩ :=
        lookup_sinsemilla h (r := o + 2 * j) (by omega) (hR.lookup j hj)
      exact ⟨m, hm, fun _ => hfacts⟩
    · exact ⟨0, by norm_num, fun h' => absurd h' hj⟩
  choose ms hms hfacts using hall
  exact ⟨ms, hms, fun j hj => hfacts j hj⟩

/-- One Sinsemilla word: the gate and the lookup facts give one step of the hash. -/
theorem sinWord_sound (h : w.Constrained S n) {r : ℕ} (hr : r < n)
    (hf : w.fLookup r = 1) {m : ℕ}
    (hx : w.a1 (r + 1) = (S m).x) (hy : w.sinYP r = (S m).y)
    {A B : Point Fp} (hstep : step S m A = some B)
    (hxa : w.a0 r = A.x) (hya : w.bigYA r = 2 * A.y) :
    w.a0 (r + 2) = B.x ∧
      (w.qS3 r = 0 → w.bigYA (r + 2) = 2 * B.y) ∧
      (w.qS3 r = 2 → w.a1 (r + 2) = B.y) := by
  have hzero : ∀ {p : Fp}, p ∈ w.sinPolys r → p = 0 := fun hp =>
    h.poly_zero (g := (w.fSin, w.sinPolys)) (by simp [gates]) hr
      (by simp [(fSin_fRc_of_one hf).1]) hp
  have hsec : w.a2 r * w.a2 r - (w.a0 (r + 2) + w.xR r + w.a0 r) = 0 :=
    hzero (by simp [sinPolys])
  have hycheck : w.a2 r * 4 * (w.a0 r - w.a0 (r + 2))
      - (w.bigYA r * 2 + (2 - w.qS3 r) * w.bigYA (r + 2) + w.qS3 r * 2 * w.a1 (r + 2)) = 0 :=
    hzero (by simp [sinPolys])
  have key : ∀ YB : Fp,
      w.a2 r * 4 * (w.a0 r - w.a0 (r + 2)) - (w.bigYA r * 2 + 2 * YB) = 0 →
      w.a0 (r + 2) = B.x ∧ YB = 2 * B.y := fun YB hY =>
    sin_step hstep (xa := w.a0 r) (l1 := w.a1 r) (l2 := w.a2 r) (xp := w.a1 (r + 1))
      hxa hya hx hy hsec hY
  refine ⟨?_, ?_, ?_⟩
  · by_cases h3 : w.qS3 r = 0
    · exact (key (w.bigYA (r + 2)) (by rw [h3] at hycheck; linear_combination hycheck)).1
    · -- any `YB` that satisfies the `y` check gives the same `x`
      have hsplit : w.a2 r * 4 * (w.a0 r - w.a0 (r + 2))
          - (w.bigYA r * 2 + 2 * (twoInv * (w.a2 r * 4 * (w.a0 r - w.a0 (r + 2))
            - w.bigYA r * 2))) = 0 := by
        have t := two_mul_twoInv
        linear_combination (-(w.a2 r * 4 * (w.a0 r - w.a0 (r + 2)) - w.bigYA r * 2)) * t
      exact (key _ hsplit).1
  · intro h3
    exact (key (w.bigYA (r + 2)) (by rw [h3] at hycheck; linear_combination hycheck)).2
  · intro h3
    have := (key (2 * w.a1 (r + 2)) (by rw [h3] at hycheck; linear_combination hycheck)).2
    exact mul_left_cancel₀ Zcash.Circuits.two_ne_zero this

theorem qS3_of_sinMode {r j : ℕ} (hm : w.fS2 r = sinMode j) (hj : j < 50) :
    w.qS3 r = 0 := by
  unfold qS3
  rw [hm]
  unfold sinMode
  split_ifs with h1 h2
  · simp
  · omega
  · simp

theorem qS3_of_sinMode_last {r : ℕ} (hm : w.fS2 r = sinMode 50) : w.qS3 r = 2 := by
  unfold qS3
  rw [hm]
  norm_num [sinMode]

/-- The hash chain: if the Sinsemilla hash of the 51 words is defined, the output
cells on row `o + 102` hold the hash point. -/
theorem sinsemilla_chain (h : w.Constrained S n) {Q : Point Fp} {o : ℕ}
    (ho : o + 104 ≤ n) (hR : w.SinsemillaRegion Q o) {ms : ℕ → ℕ}
    (hw : w.SinWords S o ms) :
    ∀ B, hashToPoint S Q ((List.range 51).map ms) = some B → w.pt01 (o + 102) = B := by
  have hinv : ∀ j, j ≤ 50 → ∀ A, hashToPoint S Q ((List.range j).map ms) = some A →
      w.a0 (o + 2 * j) = A.x ∧ w.bigYA (o + 2 * j) = 2 * A.y := by
    intro j
    induction j with
    | zero =>
      intro _ A hA
      have hQA : Q = A := by simpa [Specs.Sinsemilla.hashToPoint_nil] using hA
      subst hQA
      have hzero : ∀ {p : Fp}, p ∈ w.sinInitPolys o → p = 0 := fun hp =>
        h.poly_zero (g := (w.qSinInit, w.sinInitPolys)) (by simp [gates]) (r := o)
          (by omega) (by simp [hR.init]) hp
      have h1 : w.a0 o - w.lagrange 0 o = 0 := hzero (by simp [sinInitPolys])
      have h2 : w.lagrange 1 o * 2 - w.bigYA o = 0 := hzero (by simp [sinInitPolys])
      rw [hR.xQ] at h1
      rw [hR.yQ] at h2
      exact ⟨by simpa using sub_eq_zero.mp h1, by simp only [Nat.mul_zero, Nat.add_zero]; linear_combination -h2⟩
    | succ j ih =>
      intro hj B hB
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        Specs.Sinsemilla.hashToPoint_concat] at hB
      obtain ⟨A, hA, hstep⟩ := Option.bind_eq_some_iff.mp hB
      obtain ⟨hxa, hya⟩ := ih (by omega) A hA
      obtain ⟨-, hx, hy⟩ := hw j (by omega)
      obtain ⟨hxB, hyB, -⟩ := sinWord_sound h (r := o + 2 * j) (by omega)
        (hR.lookup j (by omega)) hx hy hstep hxa hya
      have hidx : o + 2 * (j + 1) = o + 2 * j + 2 := by ring
      rw [hidx]
      exact ⟨hxB, hyB (qS3_of_sinMode (hR.mode j (by omega)) (by omega))⟩
  intro B hB
  rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
    Specs.Sinsemilla.hashToPoint_concat] at hB
  obtain ⟨A, hA, hstep⟩ := Option.bind_eq_some_iff.mp hB
  obtain ⟨hxa, hya⟩ := hinv 50 le_rfl A hA
  obtain ⟨-, hx, hy⟩ := hw 50 (by norm_num)
  obtain ⟨hxB, -, hyB⟩ := sinWord_sound h (r := o + 2 * 50) (by omega)
    (hR.lookup 50 (by norm_num)) hx hy hstep hxa hya
  have hy' := hyB (qS3_of_sinMode_last (hR.mode 50 (by norm_num)))
  show (⟨w.a0 (o + 102), w.a1 (o + 102)⟩ : Point Fp) = B
  have hidx : o + 2 * 50 + 2 = o + 102 := by omega
  rw [hidx] at hxB hy'
  cases B
  rw [Point.mk.injEq]
  exact ⟨hxB, hy'⟩

/-- The running sums of the pieces: the `z` cell of word `j` is on row
`o + 2 j + 1`. Piece `a` is the sum of words 0 to 24, its 13th running sum is the sum
of words 13 to 24, piece `b` is word 25, piece `c` is the sum of words 26 to 49, and
piece `d` is word 50. -/
theorem sinsemilla_pieces {Q : Point Fp} {o : ℕ} (hR : w.SinsemillaRegion Q o)
    {ms : ℕ → ℕ} (hw : w.SinWords S o ms) :
    w.a0 (o + 1) = ((∑ j ∈ Finset.range 25, ms j * 2 ^ (10 * j) : ℕ) : Fp) ∧
    w.a0 (o + 27) = ((∑ j ∈ Finset.range 12, ms (13 + j) * 2 ^ (10 * j) : ℕ) : Fp) ∧
    w.a0 (o + 51) = (ms 25 : Fp) ∧
    w.a0 (o + 53) = ((∑ j ∈ Finset.range 24, ms (26 + j) * 2 ^ (10 * j) : ℕ) : Fp) ∧
    w.a0 (o + 101) = (ms 50 : Fp) := by
  -- the running-sum relation of each word, by its mode
  have hrun : ∀ j, j < 51 → j ≠ 24 → j ≠ 25 → j ≠ 49 → j ≠ 50 →
      w.a0 (o + 2 * j + 1) = (ms j : Fp) + 2 ^ 10 * w.a0 (o + 2 * (j + 1) + 1) := by
    intro j hj h24 h25 h49 h50
    have hmode : w.fS2 (o + 2 * j) = 1 := by
      rw [hR.mode j hj]; simp [sinMode, h24, h25, h49, h50]
    have := (hw j hj).1
    rw [qRun_of_one hmode] at this
    have hidx : o + 2 * (j + 1) + 1 = o + 2 * j + 3 := by ring
    rw [hidx]
    linear_combination this
  have hend : ∀ j, j < 51 → (j = 24 ∨ j = 25 ∨ j = 49 ∨ j = 50) →
      w.a0 (o + 2 * j + 1) = (ms j : Fp) := by
    intro j hj hcase
    have hq : w.qRun (o + 2 * j) = 0 := by
      rcases hcase with rfl | rfl | rfl | rfl
      · exact qRun_of_zero (by rw [hR.mode _ hj]; simp [sinMode])
      · exact qRun_of_zero (by rw [hR.mode _ hj]; simp [sinMode])
      · exact qRun_of_zero (by rw [hR.mode _ hj]; simp [sinMode])
      · exact qRun_of_two (by rw [hR.mode _ hj]; simp [sinMode])
    have := (hw j hj).1
    rw [hq] at this
    linear_combination this
  have hA := piece_sum (fun i => w.a0 (o + 2 * i + 1)) ms 25
    (fun i hi => hrun i (by omega) (by omega) (by omega) (by omega) (by omega))
    (hend 24 (by norm_num) (by simp))
  have hC := piece_sum (fun i => w.a0 (o + 2 * (26 + i) + 1)) (fun i => ms (26 + i)) 24
    (fun i hi => hrun (26 + i) (by omega) (by omega) (by omega) (by omega) (by omega))
    (hend 49 (by norm_num) (by simp))
  have h1 := hA 24 0 (by norm_num)
  have h2 := hA 11 13 (by norm_num)
  have h3 := hend 25 (by norm_num) (by simp)
  have h4 := hC 23 0 (by norm_num)
  have h5 := hend 50 (by norm_num) (by simp)
  simp only [Nat.zero_add, Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd,
    Nat.add_assoc] at h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

end Assignment

end AddressSignature
