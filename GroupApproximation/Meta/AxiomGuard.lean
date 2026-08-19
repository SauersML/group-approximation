/-
The design of this command is borrowed, with thanks, from two Apache 2.0
projects registered in the Palomar registry:

* `gexahedron/sabidussi-lean` (Copyright (c) 2026 Nikolay Ulyanov), whose
  `Sabidussi/Audit.lean` pins the axiom closure of each audited theorem with
  `#guard_msgs in #print axioms`, so that a widened closure is a compile error
  rather than a line of log output;
* `FormalFrontier/TauCeti`, whose `Scripts/Axioms.lean` carries the
  `propext / Classical.choice / Quot.sound` allowlist together with the rule
  that governance tooling must fail loudly rather than pass vacuously.

Neither file is copied.  A `#guard_msgs` fixture pins the *rendering* of a
report -- including where Lean chose to wrap the printed list -- and this
repository has five hundred audited endpoints, so the same guarantee is spelled
here as an elaborator that inspects the closure directly.
-/

import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# `#audit_axioms`: an axiom report that fails the build

`#print axioms foo` writes the transitive axiom closure of `foo` into the build
log and then succeeds, whatever it found.  A module full of them documents the
trust surface without gating it: an admission axiom in one of those lines is a
line of output, and whether anyone notices depends on whether a human reads a
five-hundred-line log.

`scripts/Audit.lean` does gate the same property over the whole corpus, but it
is a separate CI step, and a separate step is exactly what a
`continue-on-error`, a cancelled run, or a reordering can quietly remove.

`#audit_axioms foo` prints the same report and then **throws** unless the
closure is contained in the three axioms of classical Lean.  Because it is a
command elaborated inside an ordinary library module, its verdict is a
`lake build` error: every downstream module and every cached `.olean` depends
on it, and there is no step to skip.

The two checks are deliberately redundant.  This one is per-endpoint and inside
the build; `scripts/Audit.lean` sweeps every declaration of the corpus,
including the ones no `#audit_axioms` line names.
-/

open Lean Elab Command

namespace GroupApproximation.Meta

/-- The axioms of classical Lean, and the whole of what this development is
permitted to depend on.

Kept in step with `allowedAxioms` in `scripts/Audit.lean`, which enforces the
same list over every declaration of the corpus rather than at the individually
cited endpoints.  Two copies, because this one must be loadable from inside the
library and that one must be loadable without it. -/
def classicalAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Report the transitive axiom closure of `constName`, and fail if any part of
it lies outside `classicalAxioms`. -/
def auditAxiomsOf (constName : Name) : CommandElabM Unit := do
  let closure := (← collectAxioms constName).qsort Name.lt
  let bad := closure.filter fun a => !classicalAxioms.contains a
  if bad.isEmpty then
    logInfo m!"'{constName}' depends on axioms: {closure.toList}"
  else
    throwError "'{constName}' depends on axioms outside the classical allowlist: \
{bad.toList}\n  full closure: {closure.toList}\n  permitted: {classicalAxioms}"

/-- `#audit_axioms foo` is `#print axioms foo` that fails the build when the
closure of `foo` is not classical. -/
elab "#audit_axioms " id:ident : command => withRef id do
  let names ← liftCoreM <| realizeGlobalConstWithInfos id
  names.forM auditAxiomsOf

end GroupApproximation.Meta

/-! ## Calibration

A gate that has silently stopped firing is indistinguishable from a clean
corpus, so both directions are asserted here, in the module that defines the
gate, rather than in a separate calibration step that could itself be skipped.

`Lean.ofReduceBool` is the axiom a compiler-backed decision procedure
introduces.  It is named here rather than planted: this repository forbids hand-declared axioms outside
`scripts/Audit/Plants.lean`, and a calibration that needed an exception to that
rule would be a worse trade than the one it checks.  Its own closure carries
`Lean.trustCompiler` as well, which is the point of running the transitive
closure rather than testing the head. -/

/-- info: 'propext' depends on axioms: [propext] -/
#guard_msgs in
#audit_axioms propext

/--
error: 'Lean.ofReduceBool' depends on axioms outside the classical allowlist: [Lean.ofReduceBool, Lean.trustCompiler]
  full closure: [Lean.ofReduceBool, Lean.trustCompiler]
  permitted: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#audit_axioms Lean.ofReduceBool
