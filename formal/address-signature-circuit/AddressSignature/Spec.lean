import AddressSignature.Imports

/-!
# The Address signature statement

The statement of the draft ZIP "Orchard address signatures", section "Address
signature statement": spend authority and diversified address integrity, with
`g_d`, `pk_d`, `rk` as the primary input.

The definitions come from the Ironwood formalization: the Pallas curve and its
group law, the certified fixed bases `SpendAuthG` and `CommitIvkR`, the Sinsemilla
generator table, and the `Commit^ivk` message encoding. The two conditions have the
shape of the conditions of the same name in Ironwood's `ActionSpec`
(`Zcash/Circuits/Action/Spec.lean`).
-/

namespace AddressSignature

open Zcash.Circuits
open Zcash.Circuits.Specs.Sinsemilla (hashToPoint commitIvkChunks HashGuarded)

/-- The Pallas scalar field. -/
abbrev Fq := CompElliptic.Fields.Pasta.Fq

/-- The spend authorization base `G^SpendAuth`, with its certified window tables. -/
abbrev spendAuthG : Ecc.MulFixed.FixedBase := Ecc.MulFixed.Certs.spendAuthG

/-- The `Commit^ivk` randomness base `R`, with its certified window tables. -/
abbrev commitIvkR : Ecc.MulFixed.FixedBase := Ecc.MulFixed.Certs.commitIvkR

/-- The Sinsemilla generator table `S`. -/
abbrev generators : Specs.Sinsemilla.Generators := Specs.Sinsemilla.orchardGenerators

/-- The Sinsemilla initial point `Q` of the `Commit^ivk` domain:
`Q_COMMIT_IVK_M_GENERATOR` of `crates/orchard/src/constants/sinsemilla.rs`. It has
the value of `ivkQ` of Ironwood's `Zcash/Circuits/Action/RealBases.lean`. -/
def ivkQ : Point Fp :=
  { x := (2593820817260930114322133467408868473290945477826616247349533151445648376562 : Fp),
    y := (12214744946019415453501880094709511126888074367290315326445800415816181472958 : Fp) }

theorem ivkQ_onCurve : ivkQ.OnCurve := by
  show ivkQ.y ^ 2 = ivkQ.x ^ 3 + pallasB
  decide

/-- `Commit^ivk_rivk(ak, nk)`: the `x`-coordinate of
`SinsemillaHashToPoint(I2LEBSP_255(ak) ‖ I2LEBSP_255(nk)) + [rivk] R`, or `⊥` (`none`)
if the hash is `⊥`. `ak` and `nk` are encoded by their canonical integers. -/
def commitIvk (ak nk : Fp) (rivk : Fq) : Option Fp :=
  (hashToPoint generators.S ivkQ (commitIvkChunks ak.val nk.val)).map
    fun hashPoint => (hashPoint + rivk • commitIvkR).x

/-- The Address signature statement for the primary input `(g_d, pk_d, rk)`.

* `g_d` and `pk_d` are non-identity Pallas points.
* There is an auxiliary input `(ak_P, α, nk, rivk)` with `ak_P` a non-identity Pallas
  point, such that:
  * **Spend authority**: `rk = [α] G^SpendAuth + ak_P`.
  * **Diversified address integrity**: `ivk = ⊥` or `pk_d = [ivk] g_d`, where
    `ivk = Commit^ivk_rivk(Extract(ak_P), nk)`.

The scalar `α` is an element of the scalar field: `[α] G` depends only on `α` modulo
the group order. `[ivk] g_d` uses the canonical integer of `ivk`. -/
def Statement (gd pkd rk : Point Fp) : Prop :=
  gd.OnCurve ∧ pkd.OnCurve ∧
  ∃ (akP : Point Fp) (alpha : Fq) (nk : Fp) (rivk : Fq),
    akP.OnCurve ∧
    rk = alpha • spendAuthG + akP ∧
    (commitIvk akP.x nk rivk = none ∨
      ∃ ivk : Fp, commitIvk akP.x nk rivk = some ivk ∧ pkd = ivk.val • gd)

/-- The statement in the shape of Ironwood's `ActionSpec`. There is always an `ivk`
with `pk_d = [ivk] g_d`; if the Sinsemilla hash is defined, this `ivk` is the
commitment. This form implies `Statement`. -/
def StatementGuarded (gd pkd rk : Point Fp) : Prop :=
  gd.OnCurve ∧ pkd.OnCurve ∧
  ∃ (akP : Point Fp) (alpha : Fq) (nk : Fp) (rivk : Fq),
    akP.OnCurve ∧
    rk = alpha • spendAuthG + akP ∧
    ∃ ivk : Fp,
      HashGuarded generators.S ivkQ (commitIvkChunks akP.x.val nk.val)
        (fun hashPoint => ivk = (hashPoint + rivk • commitIvkR).x) ∧
      pkd = ivk.val • gd

theorem Statement.of_guarded {gd pkd rk : Point Fp} (h : StatementGuarded gd pkd rk) :
    Statement gd pkd rk := by
  obtain ⟨hgd, hpkd, akP, alpha, nk, rivk, hak, hrk, ivk, hguard, hmul⟩ := h
  refine ⟨hgd, hpkd, akP, alpha, nk, rivk, hak, hrk, ?_⟩
  unfold commitIvk
  cases hhash : hashToPoint generators.S ivkQ (commitIvkChunks akP.x.val nk.val) with
  | none => exact Or.inl rfl
  | some hashPoint =>
    refine Or.inr ⟨ivk, ?_, hmul⟩
    rw [hguard hashPoint hhash]
    rfl

end AddressSignature
