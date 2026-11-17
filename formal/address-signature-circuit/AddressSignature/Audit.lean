import AddressSignature.PinnedSoundness

/-!
# Axiom audit

The build fails if a main theorem depends on an axiom that is not in the list. The
list has the three standard axioms of Lean and Mathlib, and one `native_decide`
axiom of CompElliptic: the computation `[q] G = O` for the Pallas generator, which
CompElliptic uses to prove that the Pallas group has prime order `q`.
-/

open Lean Elab Command in
/-- `assert_axioms thm [ax₁, …]` fails if `thm` depends on an axiom outside the list. -/
elab "assert_axioms " thm:ident " [" allowed:ident,* "]" : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo thm
  let allowedNames := allowed.getElems.map (·.getId)
  let axioms ← liftCoreM <| collectAxioms name
  let extra := axioms.filter fun a => !allowedNames.contains a
  unless extra.isEmpty do
    throwError "{name} depends on axioms that are not allowed: {extra}"
  logInfo m!"{name}: axioms {axioms}"

assert_axioms AddressSignature.soundness
  [propext, Classical.choice, Quot.sound,
   CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt._native.native_decide.ax_1_1]

assert_axioms AddressSignature.soundness_guarded
  [propext, Classical.choice, Quot.sound,
   CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt._native.native_decide.ax_1_1]

assert_axioms AddressSignature.soundness_pinned
  [propext, Classical.choice, Quot.sound,
   CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt._native.native_decide.ax_1_1]

assert_axioms AddressSignature.soundness_explicit
  [propext, Classical.choice, Quot.sound,
   CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt._native.native_decide.ax_1_1]

assert_axioms AddressSignature.soundness_pinned_explicit
  [propext, Classical.choice, Quot.sound,
   CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt._native.native_decide.ax_1_1]
