import AddressSignature.Layout

/-!
# Soundness of the address signature circuit

If an assignment satisfies all gate constraints, the lookup, and the copy
constraints of the circuit, the primary input `(g_d, pk_d, rk)` in the instance
column satisfies the Address signature statement.
-/

namespace AddressSignature

open Zcash.Circuits
open Zcash.Circuits.Specs.Sinsemilla (hashToPoint commitIvkChunks)
open Zcash.Circuits.Ecc.MulFixed (Cert.cast_eq_zero_iff)

/-! ## `z + 1` is not zero (shortcut 1) -/

private theorem spendAuthG_z_check :
    (List.range 85).all
      (fun j => decide (Ecc.MulFixed.Certs.spendAuthGCert.zs[j]! + 1 < Ecc.MulFixed.Cert.P))
      = true := by
  decide +kernel

private theorem commitIvkR_z_check :
    (List.range 85).all
      (fun j => decide (Ecc.MulFixed.Certs.commitIvkRCert.zs[j]! + 1 < Ecc.MulFixed.Cert.P))
      = true := by
  decide +kernel

/-- For each window of `G^SpendAuth`, `z + 1` is not zero in the base field. The
fixed column `fixed_z_plus_one` is thus not zero on a window row. -/
theorem spendAuthG_z_ne (j : ℕ) (hj : j < 85) : (spendAuthG.params j).z + 1 ≠ 0 := by
  have hlt := of_decide_eq_true
    (List.all_eq_true.mp spendAuthG_z_check j (List.mem_range.mpr hj))
  show ((Ecc.MulFixed.Certs.spendAuthGCert.zs[j]! : ℕ) : Fp) + 1 ≠ 0
  intro h0
  have hcast : ((Ecc.MulFixed.Certs.spendAuthGCert.zs[j]! + 1 : ℕ) : Fp) = 0 := by
    push_cast; exact h0
  rw [Cert.cast_eq_zero_iff hlt] at hcast
  omega

/-- For each window of `R`, `z + 1` is not zero in the base field. -/
theorem commitIvkR_z_ne (j : ℕ) (hj : j < 85) : (commitIvkR.params j).z + 1 ≠ 0 := by
  have hlt := of_decide_eq_true
    (List.all_eq_true.mp commitIvkR_z_check j (List.mem_range.mpr hj))
  show ((Ecc.MulFixed.Certs.commitIvkRCert.zs[j]! : ℕ) : Fp) + 1 ≠ 0
  intro h0
  have hcast : ((Ecc.MulFixed.Certs.commitIvkRCert.zs[j]! + 1 : ℕ) : Fp) = 0 := by
    push_cast; exact h0
  rw [Cert.cast_eq_zero_iff hlt] at hcast
  omega

/-! ## The main theorem -/

/-- **Soundness, in the shape of Ironwood's `ActionSpec`.** -/
theorem soundness_guarded (w : Assignment) (L : Placement) (n : ℕ)
    (hC : w.Constrained generators.S n) (hW : Wired w L n) :
    StatementGuarded ⟨w.inst 0, w.inst 1⟩ ⟨w.inst 2, w.inst 3⟩ ⟨w.inst 4, w.inst 5⟩ := by
  -- `g_d` and `ak_P` are points on the curve
  have hgd : (w.pt01 L.gd).OnCurve :=
    Assignment.point_sound hC (by have := hW.fitsGd; omega) hW.gdSel
  have hak : (w.pt01 L.ak).OnCurve :=
    Assignment.point_sound hC (by have := hW.fitsAk; omega) hW.akSel
  have hgdInst : (⟨w.inst 0, w.inst 1⟩ : Point Fp) = w.pt01 L.gd := by
    rw [← hW.gdX, ← hW.gdY]; rfl
  -- spend authority
  obtain ⟨alpha, halpha⟩ := Assignment.fixedMul_sound hC spendAuthG spendAuthG_z_ne
    hW.fitsAlphaMul hW.fitsAlphaAdd hW.alphaMul hW.alphaAddSel hW.alphaAddP hW.alphaAddQ
  have hrk : w.pt01 (L.rkAdd + 2) = alpha • spendAuthG + w.pt01 L.ak := by
    rw [Assignment.add_sound hC (by have := hW.fitsRkAdd; omega) hW.rkSel
      (by rw [hW.rkP, halpha]; exact spendAuthG.smul_valid alpha)
      (by rw [hW.rkQ]; exact Or.inl hak), hW.rkP, hW.rkQ, halpha]
  have hrkInst : (⟨w.inst 4, w.inst 5⟩ : Point Fp) = w.pt01 (L.rkAdd + 2) := by
    rw [← hW.rkX, ← hW.rkY]; rfl
  -- `Commit^ivk`
  obtain ⟨rivk, hrivk⟩ := Assignment.fixedMul_sound hC commitIvkR commitIvkR_z_ne
    hW.fitsRivkMul hW.fitsRivkAdd hW.rivkMul hW.rivkAddSel hW.rivkAddP hW.rivkAddQ
  have hhash := Assignment.commitIvk_hash_sound hC (Q := ivkQ)
    hW.fitsHash hW.fitsB0 hW.fitsB2 hW.fitsD0 hW.fitsAPrime hW.fitsB2cPrime
    hW.fitsCanonAk hW.fitsCanonNk hW.hash hW.b0 hW.b2 hW.d0 hW.aPrime hW.b2cPrime hW.canon
  have hakx : w.a0 L.canonAk = (w.pt01 L.ak).x := hW.canonAkCopy
  rw [hakx] at hhash
  -- `[ivk] g_d`
  have hmul := Assignment.mul_sound hC hW.fitsMul hW.mul hgd hW.mulBase
  rw [hW.mulScalar] at hmul
  -- `pk_d`
  have hpkd : (w.pt01 L.pkd).OnCurve :=
    Assignment.point_sound hC (by have := hW.fitsPkd; omega) hW.pkdSel
  have hpkdInst : (⟨w.inst 2, w.inst 3⟩ : Point Fp) = w.pt01 L.pkd := by
    rw [← hW.pkdX, ← hW.pkdY]; rfl
  rw [hgdInst, hpkdInst, hrkInst]
  refine ⟨hgd, hpkd, w.pt01 L.ak, alpha, w.a0 L.canonNk, rivk, hak, hrk,
    w.a0 (L.commitAdd + 2), ?_, ?_⟩
  · intro hashPoint hdef
    have hout := hhash hashPoint hdef
    have hvalid : hashPoint.Valid :=
      Specs.Sinsemilla.hashToPoint_valid (G := generators) (Or.inl ivkQ_onCurve)
        (fun m hm => Specs.Sinsemilla.chunksOf_mem_lt hm) hdef
    have hadd := Assignment.add_sound hC (r := L.commitAdd)
      (by have := hW.fitsCommitAdd; omega) hW.commitSel
      (by rw [hW.commitP, hout]; exact hvalid)
      (by rw [hW.commitQ, hrivk]; exact commitIvkR.smul_valid rivk)
    rw [hW.commitP, hW.commitQ, hout, hrivk] at hadd
    exact congrArg Point.x hadd
  · rw [hW.pkdCopy]
    exact hmul

open Zcash.Circuits.Specs.Sinsemilla (HashGuarded) in
/-- **Soundness of the address signature circuit, with the witness in named cells.**

This is the main theorem. The conclusion names the cells of the assignment that hold
the auxiliary input, so it is a statement about the witness that the prover committed
to, and not only about the primary input.

Let `w` be an assignment of the circuit columns, `L` a placement of the regions, and
`n` the number of usable rows. If all 15 gates and the lookup hold on the first `n`
rows (`hC`), and the fixed cells and copy constraints are those of
`Circuit::synthesize` (`hW`), then:

* rows 0 to 5 of the instance column are the cells of `g_d`, `pk_d`, and `rk`;
* the cells of `g_d`, `pk_d`, and `ak_P` are points on the curve, and thus not the
  identity;
* there are scalars `alpha` and `rivk`, and they are the scalars of the two
  fixed-base multiplications: the result cells of those multiplications are
  `[alpha] G^SpendAuth` and `[rivk] R`;
* `rk = [alpha] G^SpendAuth + ak_P`;
* if the Sinsemilla hash of `ak ‖ nk` is not `⊥`, the `ivk` cell is the
  `x`-coordinate of the hash point plus `[rivk] R`, where `ak` is the `x`-coordinate
  of the `ak_P` cell and `nk` is the `nk` cell, both as canonical integers;
* `pk_d = [ivk] g_d`, with the canonical integer of the `ivk` cell.

`soundness` below is the same result with the witness under an existential
quantifier, in the form of the ZIP statement. -/
theorem soundness_explicit (w : Assignment) (L : Placement) (n : ℕ)
    (hC : w.Constrained generators.S n) (hW : Wired w L n) :
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
      w.pt01 L.pkd = (w.a0 (L.commitAdd + 2)).val • w.pt01 L.gd := by
  have hgd : (w.pt01 L.gd).OnCurve :=
    Assignment.point_sound hC (by have := hW.fitsGd; omega) hW.gdSel
  have hak : (w.pt01 L.ak).OnCurve :=
    Assignment.point_sound hC (by have := hW.fitsAk; omega) hW.akSel
  have hgdInst : (⟨w.inst 0, w.inst 1⟩ : Point Fp) = w.pt01 L.gd := by
    rw [← hW.gdX, ← hW.gdY]; rfl
  obtain ⟨alpha, halpha⟩ := Assignment.fixedMul_sound hC spendAuthG spendAuthG_z_ne
    hW.fitsAlphaMul hW.fitsAlphaAdd hW.alphaMul hW.alphaAddSel hW.alphaAddP hW.alphaAddQ
  have hrk : w.pt01 (L.rkAdd + 2) = alpha • spendAuthG + w.pt01 L.ak := by
    rw [Assignment.add_sound hC (by have := hW.fitsRkAdd; omega) hW.rkSel
      (by rw [hW.rkP, halpha]; exact spendAuthG.smul_valid alpha)
      (by rw [hW.rkQ]; exact Or.inl hak), hW.rkP, hW.rkQ, halpha]
  have hrkInst : (⟨w.inst 4, w.inst 5⟩ : Point Fp) = w.pt01 (L.rkAdd + 2) := by
    rw [← hW.rkX, ← hW.rkY]; rfl
  obtain ⟨rivk, hrivk⟩ := Assignment.fixedMul_sound hC commitIvkR commitIvkR_z_ne
    hW.fitsRivkMul hW.fitsRivkAdd hW.rivkMul hW.rivkAddSel hW.rivkAddP hW.rivkAddQ
  have hhash := Assignment.commitIvk_hash_sound hC (Q := ivkQ)
    hW.fitsHash hW.fitsB0 hW.fitsB2 hW.fitsD0 hW.fitsAPrime hW.fitsB2cPrime
    hW.fitsCanonAk hW.fitsCanonNk hW.hash hW.b0 hW.b2 hW.d0 hW.aPrime hW.b2cPrime hW.canon
  have hakx : w.a0 L.canonAk = (w.pt01 L.ak).x := hW.canonAkCopy
  rw [hakx] at hhash
  have hmul := Assignment.mul_sound hC hW.fitsMul hW.mul hgd hW.mulBase
  rw [hW.mulScalar] at hmul
  have hpkd : (w.pt01 L.pkd).OnCurve :=
    Assignment.point_sound hC (by have := hW.fitsPkd; omega) hW.pkdSel
  have hpkdInst : (⟨w.inst 2, w.inst 3⟩ : Point Fp) = w.pt01 L.pkd := by
    rw [← hW.pkdX, ← hW.pkdY]; rfl
  refine ⟨hgdInst, hpkdInst, hrkInst, hgd, hpkd, hak, alpha, rivk, halpha, hrivk, hrk, ?_, ?_⟩
  · intro hashPoint hdef
    have hout := hhash hashPoint hdef
    have hvalid : hashPoint.Valid :=
      Specs.Sinsemilla.hashToPoint_valid (G := generators) (Or.inl ivkQ_onCurve)
        (fun m hm => Specs.Sinsemilla.chunksOf_mem_lt hm) hdef
    have hadd := Assignment.add_sound hC (r := L.commitAdd)
      (by have := hW.fitsCommitAdd; omega) hW.commitSel
      (by rw [hW.commitP, hout]; exact hvalid)
      (by rw [hW.commitQ, hrivk]; exact commitIvkR.smul_valid rivk)
    rw [hW.commitP, hW.commitQ, hout, hrivk] at hadd
    exact congrArg Point.x hadd
  · rw [hW.pkdCopy]
    exact hmul

/-- **Soundness of the address signature circuit.**

Let `w` be an assignment of the circuit columns, `L` a placement of the regions, and
`n` the number of usable rows. If

* all 15 gates and the lookup hold on the first `n` rows (`hC`), and
* the fixed cells and copy constraints are those of `Circuit::synthesize` (`hW`),

then the primary input `(g_d, pk_d, rk)` in rows 0 to 5 of the instance column
satisfies the Address signature statement.

This form puts the auxiliary input under an existential quantifier. As a statement
about the primary input alone it is weak. `soundness_explicit` is the form to use: it
says which cells hold the auxiliary input. -/
theorem soundness (w : Assignment) (L : Placement) (n : ℕ)
    (hC : w.Constrained generators.S n) (hW : Wired w L n) :
    Statement ⟨w.inst 0, w.inst 1⟩ ⟨w.inst 2, w.inst 3⟩ ⟨w.inst 4, w.inst 5⟩ :=
  Statement.of_guarded (soundness_guarded w L n hC hW)

end AddressSignature
