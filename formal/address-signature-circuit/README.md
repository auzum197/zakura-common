# Soundness of the Orchard address signature circuit, in Lean 4

This project proves that the narrow address signature circuit
(`crates/orchard/src/circuit/halo2/address_signature/`) enforces the Address signature
statement of the draft ZIP "Orchard address signatures".

**Main theorem** (`AddressSignature.soundness_pinned_explicit`, in
`AddressSignature/PinnedSoundness.lean`). If an assignment satisfies the 15 gates and
the lookup of the pinned circuit description, and the fixed cells and copy constraints
are those of `Circuit::synthesize`, then the statement below holds for the values in
named cells of the assignment: the cells of `ak_P`, `nk`, and `ivk`, and the result
cells of the two fixed-base multiplications, which fix `α` and `rivk`.

`AddressSignature.soundness_pinned` is the same result with the auxiliary input under
an existential quantifier, in the form of the ZIP statement. That form does not say
which cells hold the auxiliary input, so as a statement about the primary input alone
it is weak. Use the explicit form.

The primary input `(g_d, pk_d, rk)` satisfies:

- `g_d` and `pk_d` are non-identity Pallas points;
- there are `ak_P` (a non-identity Pallas point), `α`, `nk`, `rivk` such that
  - `rk = [α] G^SpendAuth + ak_P`, and
  - `ivk = ⊥`, or `pk_d = [ivk] g_d`, where
    `ivk = Commit^ivk_rivk(Extract(ak_P), nk)` over the canonical encodings of `ak`
    and `nk`, and `[ivk]` uses the canonical integer of `ivk`.

The proof has no `sorry` and adds no axiom. Read [ASSUMPTIONS.md](ASSUMPTIONS.md) for
what it assumes.

The layout in Lean (selector rows, fixed cells, copy constraints) is a transcription
of the Rust synthesis code. `scripts/check_layout.py` compares it, in both directions,
with `fixtures/addressSignatureLayout.json`, which a Rust test records from the real
circuit. The script has its own copy of the facts and does not read the Lean file, so
this check is outside the Lean kernel.

## Build

The project builds on the Ironwood formalization (`github.com/zcash/ironwood`), which
needs Lean 4.30.0. `elan` installs that toolchain from `lean-toolchain`.

```sh
cd formal/address-signature-circuit
lake exe cache get     # one time: download the Mathlib build
lake build             # the first build compiles about 110 Ironwood modules (5 minutes)
python3 scripts/pinned.py --check \
    ../../crates/orchard/src/circuit_data/circuit_description_address_signature_v1 \
    AddressSignature/Pinned.lean
python3 scripts/check_constants.py
python3 scripts/check_layout.py
```

`lake build` checks all proofs and the axiom list. The two scripts check that the
generated file and the constants agree with the Rust sources.

If the circuit changes, generate `Pinned.lean` again and build:

```sh
python3 scripts/pinned.py \
    ../../crates/orchard/src/circuit_data/circuit_description_address_signature_v1 \
    AddressSignature/Pinned.lean
lake build
```

A change of a gate then fails in `PinnedCheck.lean`. A change of the layout (rows,
selectors, copy constraints) is not found: update `Layout.lean` and the region
structures manually.

## Files

| File | Content |
| --- | --- |
| `Gates.lean` | The model: columns, the 15 gates (60 polynomials), the lookup. |
| `Spec.lean` | The Address signature statement. |
| `Gadgets/Add.lean` | Non-identity point gate. Complete addition. |
| `Gadgets/FixedMul.lean` | Fixed-base multiplication: window gate (shortcut 1), incomplete addition, last window. |
| `Gadgets/Lookup.lean` | The merged lookup (shortcut 2). Range checks through the generator table. |
| `Gadgets/Sinsemilla.lean` | The Sinsemilla hash: words, running sums of the pieces, the hash chain (shortcut 3). |
| `Gadgets/CommitIvk.lean` | Canonicity of `ak` and `nk`. The hashed words are those of `ak ‖ nk`. |
| `Gadgets/MulIncomplete.lean` | Variable-base multiplication: the chain of 251 incomplete steps. |
| `Gadgets/Mul.lean` | Complete bits and the least significant bit. |
| `Gadgets/MulFull.lean` | The overflow check. The result is `[ivk] g_d` for the canonical `ivk`. |
| `Layout.lean` | The 32 regions, their fixed cells and copy constraints. |
| `Soundness.lean` | The composition. `z + 1 ≠ 0` for both fixed bases. |
| `Pinned.lean` | Generated: the polynomials of the pinned description. |
| `PinnedCheck.lean` | The model has the polynomials of the pinned description. |
| `PinnedSoundness.lean` | Soundness for the packed selector columns of the description. |
| `Audit.lean` | The allowed axioms. |

## What comes from Ironwood

- Definitions: the Pallas fields and curve, the group law, `Point`, scalar
  multiplication, the Sinsemilla specification and generator table, `commitIvkChunks`,
  the certified fixed bases `spendAuthG` and `commitIvkR`.
- Facts about the curve: prime group order, no point with `x = 0` or `y = 0`,
  different multiples have different `x`-coordinates.
- Lemmas about the constraint equations of the audited gates, as equations between
  field elements: `Add.add_of_spec`, `AddIncomplete.Gate.eq_nondegenerateAdd_of_polys_zero`,
  `DoubleAndAdd.coordinates_of_constraints`, `MulFixed.FixedBase.coords_eq_windowPoint`,
  `Mul.Incomplete.DoubleAndAdd.soundness_aux`, `Mul.k_canonical`,
  `CommitIvk.Gate.soundness_ak`, `CommitIvk.Gate.soundness_nk`,
  `CommitIvk.commitIvkChunks_eq_of_piece_digit_sums`.

Ironwood proves the Action circuit in the Clean DSL, for the layout of the audited
chips. The narrow circuit has a different layout, so this project has its own model of
the cells, the selectors, the fixed columns, and the copy constraints. It uses the
Ironwood lemmas only where a lemma is about values and not about the layout.

## The three fixed-column shortcuts and the merged lookup

| Shortcut | Where it is proved |
| --- | --- |
| `fixed_z_plus_one` is the selector of the window gate, and `z = column - 1` | `fixedWindow_sound` uses `(B.params j).z + 1 ≠ 0`. `spendAuthG_z_ne` and `commitIvkR_z_ne` prove it for the 85 windows of each base. |
| One ternary selector `f_lookup` | `fSin_fRc_of_one` and `fSin_fRc_of_two` give `(f_sin, f_rc) = (1, 0)` and `(0, 1)`. Soundness uses only the rows where `f_lookup` is 1 or 2. |
| Data in the Lagrange columns | Each reader takes the value from the fixed cell of its own row: `SinsemillaRegion.xQ`, `.yQ`, `.mode`, `ShortRangeCheckRegion.factor`, `RangeCheckRegion.mode`, `FixedMulRegion.params`. |
| Range checks in the Sinsemilla lookup | `lookup_rangeCheck`: on a row with `f_lookup = 2`, the word is below `2^10`, for all values of `a1` and `a2`. |
