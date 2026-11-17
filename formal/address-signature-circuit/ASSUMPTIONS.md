# Assumptions of the soundness proof

This file lists everything that the Lean proof of
`AddressSignature.soundness_pinned_explicit` (the main theorem), `AddressSignature.soundness_explicit`,
`AddressSignature.soundness`, and `AddressSignature.soundness_pinned` does not prove.

## 1. Lean axioms and `sorry`

There is no `sorry` and no `axiom` declaration in this project.

`AddressSignature/Audit.lean` fails the build if a main theorem depends on an axiom
outside this list:

| Axiom | Origin | Why it is there |
| --- | --- | --- |
| `propext`, `Classical.choice`, `Quot.sound` | Lean core | The standard axioms of Lean and Mathlib. |
| `CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt._native.native_decide.ax_1_1` | CompElliptic, through Ironwood | One `native_decide` computation: `[q] G = O` for the Pallas generator `G = (-1, 2)`. CompElliptic uses it to prove that the Pallas group has prime order `q`. It trusts the Lean compiler for this one computation. |

The primality of the two Pasta moduli, the fact that no Pallas point has `x = 0` or
`y = 0`, the window tables of `SpendAuthG` and `CommitIvkR`, and the on-curve check
of the 1,024 Sinsemilla generators come from Ironwood and CompElliptic. They are
proved there, in the kernel, and add no axiom.

## 2. Hypotheses of the theorem

The theorem has the form "if the assignment satisfies the constraint system, the
primary input satisfies the statement". Its hypotheses are explicit Lean
propositions:

| Hypothesis | Meaning |
| --- | --- |
| `Pinned.Constrained w c n` (or `Assignment.Constrained`) | All 15 gates and the lookup hold on the first `n` rows. |
| `SelectorsPacked w c` | The 13 binary selectors are the indicators of the 3 packed selector columns. |
| `Wired w L n` | The fixed cells and the copy constraints are those that `Circuit::synthesize` creates, for some placement `L` of the 32 regions in the first `n` rows. |

The proof holds for every placement `L` and every `n`. It does not use that regions
are disjoint. It does not use that a fixed cell is zero outside the regions.

## 3. What ties the model to the Rust circuit

### 3.1 Checked by Lean

`AddressSignature/Pinned.lean` is generated from the pinned circuit description
`crates/orchard/src/circuit_data/circuit_description_address_signature_v1`.
`AddressSignature/PinnedCheck.lean` proves:

- each of the 60 constraint polynomials of the description is equal to the
  polynomial of the model in `Gates.lean`;
- the 3 input expressions of the lookup are equal to those of the model;
- the default row of the lookup, `(0, x(S_0), y(S_0))`, is the first generator of
  Ironwood's table;
- the selector expression of each gate is not zero for the value that enables it;
- `fixed_z_plus_one` is the selector of the window gate, and `f_sin` is the selector
  of the Sinsemilla gate.

`AddressSignature/Soundness.lean` proves that `z + 1` is not zero for each of the 85
windows of both fixed bases (shortcut 1).

### 3.2 Checked by scripts

- `scripts/pinned.py --check` fails if `Pinned.lean` is not the output for the
  current pinned description. The script also checks the structure of the
  description: 16 fixed, 3 advice, 1 instance column; 13 selectors; 60 polynomials
  in 15 groups of the expected sizes, each group with one selector; one lookup with
  3 expressions into the table columns 10, 11, 12; the permutation argument over
  the 3 advice columns and the instance column.
- `scripts/check_constants.py` compares the constants of the proof with the Rust
  sources: the 1,024 Sinsemilla generators, the point `Q` of `Commit^ivk`, and the
  generator, the 85 `z` values and the 680 `u` values of `SpendAuthG` and
  `CommitIvkR`.

### 3.3 Not checked: assumed

1. **The Halo 2 proof system is sound.** A proof that the verifier accepts implies
   that an assignment exists that satisfies the gates, the lookup, and the
   permutation argument on the usable rows, with the fixed columns of the verifying
   key. This proof starts from that assignment.
2. **`Wired` is what `Circuit::synthesize` does.** The layout in `Layout.lean` and
   in the region structures of `Gadgets/` is a manual transcription of the Rust
   code: which selector is enabled on which row of a region, which fixed cell holds
   which value, and which cells a copy constraint joins. I compared each of the 32
   regions with the Rust code two times.
   - `scripts/check_layout.py` now compares these facts, in both directions, with
     `fixtures/addressSignatureLayout.json`. The Rust test
     `dump_address_signature_fixtures` records that file from the real `configure`
     and `synthesize`, with the recorder that the Action circuit uses for its
     Ironwood fixtures. The check passes: 198 checks, 0 failures.
   - What stays unchecked: the script has its own copy of the facts of `Wired`. It
     does not read `Layout.lean`, and Lean does not read the fixture. The check is
     outside the Lean kernel. A change of `Wired` needs the same change in the
     script.
   - The fixture is not pinned by a Rust test. Record it again after a change of
     the circuit, and run the script.
3. **The floor planner gives each region its own rows.** Each region assigns cells
   in column `a0`, so two regions do not share a row. If they did, a fixed cell of
   one region could replace a fixed cell of another, and `Wired` would be false.
4. **Selector packing.** Halo 2 gives each packed column the value `i` on the rows
   where selector `i` of that column is enabled. The indices come from the selector
   expressions of the pinned description (`Pinned.selectorTable`).
5. **The table.** The three table columns hold `(i, x(S_i), y(S_i))` for `i < 1024`,
   and Halo 2 fills the other rows with a copy of an assigned row. The lookup
   hypothesis is: on each usable row, the three input expressions are one of these
   1,024 rows.
6. **The Lagrange coefficients.** The Rust code computes them at run time. Ironwood
   has them as constants, with a proof that each window polynomial passes through
   the 8 points of the window. A polynomial of degree 7 through 8 points is unique,
   so the two sets are equal if the Rust computation is correct.
7. **The pinned description is the description of the verifying key in use.** The
   Rust tests pin it and its fingerprint.
8. **The instance encoding.** The verifier puts `x(g_d), y(g_d), x(pk_d), y(pk_d),
   x(rk), y(rk)` in rows 0 to 5 of the instance column.

## 4. Definitions that the statement relies on

The statement (`Spec.lean`) uses definitions of the Ironwood formalization
(`github.com/zcash/ironwood`, commit `ab5d90f5`) and of its dependencies CompElliptic,
Clean, and Mathlib. The result means what it says only if these definitions are
correct:

- the Pallas base and scalar fields, the curve `y² = x³ + 5`, and the group law on
  affine points, with the identity as `(0, 0)`;
- scalar multiplication `n • P`, and `α • B` for a fixed base;
- `SinsemillaHashToPoint` with incomplete addition, where `⊥` is `none`;
- the `Commit^ivk` message `I2LEBSP_255(ak) ‖ I2LEBSP_255(nk)` as 51 words of 10 bits
  (`commitIvkChunks`);
- the fixed bases `SpendAuthG` and `CommitIvkR`, and the generator table.

`Statement` is my transcription of the section "Address signature statement" of the
draft ZIP. Two points need attention:

- `α` is an element of the scalar field. The ZIP has `α` in `{0 .. 2^255 - 1}`. The
  two are equivalent, because `[α] G` depends only on `α` modulo the group order.
- The condition is "`ivk = ⊥` or `pk_d = [ivk] g_d`", as in the ZIP. `StatementGuarded`
  is the stronger form of Ironwood's `ActionSpec`, and the proof gives it.

## 5. Cryptographic assumptions

The proof uses no cryptographic assumption. It proves the statement of the ZIP as
written.

That statement holds trivially when `ivk = ⊥`. A prover that knows `ak` and `nk` with
`SinsemillaHashToPoint(ak ‖ nk) = ⊥` can satisfy the circuit for a `pk_d` that is not
bound to the commitment. The Action circuit has the same property. To find such an
input gives a discrete logarithm relation between the Sinsemilla generators and `Q`
(protocol specification, Theorem 5.4.4). The security of the signature scheme thus
needs:

- the discrete logarithm assumption on Pallas for the Sinsemilla generators (for the
  `⊥` case and for collision resistance of `Commit^ivk`);
- the security of RedPallas and of the address derivation, which are outside the
  circuit.

## 6. Not in scope

- Completeness: an honest prover can satisfy the circuit.
- Zero knowledge.
- The receive authority scheme, the message digest, and the RedPallas signature.
- The Rust witness generation, and the encoding and decoding of points and proofs.
