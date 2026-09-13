import Palomar.TypeA2Solution
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# The axiom closure of the FFWZ Question 5.8 theorem

`lake env lean scripts/PalomarTypeA2Axioms.lean`, run by
`.github/workflows/palomar-check.yml` after the Palomar libraries build.  The
siblings `scripts/PalomarLIXStrongAxioms.lean` and
`scripts/PalomarPestov91Axioms.lean` do the same for the other pending
configurations.

## Why this one gates although its configuration is pending

`Palomar/comparator-type-a2.json` is not submittable yet.  Its solution derives
the selected statement from `GroupApproximation.TypeA2.Question58`, which the
development does not prove yet, so the challenge and solution signatures do not
match and `scripts/check_palomar_submission.py` lists the configuration as
pending.

The `_of` form is sorry-free: the outstanding proposition is a hypothesis, not a
hole.  So a `sorryAx` reaching it through the translation layer of
`Palomar/TypeA2Solution.lean` is a real defect today, and no `sorry` scan of
that file can see it.

## Why the name carries `_of`

The configuration selects `FFWZ.exists_isTypeA2_quotient_not_isFinitelyPresented`,
and the solution does not declare that name yet.  What it declares is that
theorem with the outstanding proposition in front, under the name with `_of`
appended.  When the proposition is proved, the solution gains the unsuffixed
theorem and the list below is rewritten to the configuration's name, in the
same change that moves the configuration to `PALOMAR_CONFIGS`.
-/

open Lean Elab Command

namespace PalomarTypeA2Axioms

/-- The declaration that stands in, while the configuration is pending, for the
theorem `Palomar/comparator-type-a2.json` selects: that theorem with the one
outstanding proposition as a leading hypothesis. -/
def compared : List Name :=
  [`FFWZ.exists_isTypeA2_quotient_not_isFinitelyPresented_of]

/-- The axioms `Palomar/comparator-type-a2.json` permits, which
`scripts/check_palomar_submission.py` independently pins to exactly the three
classical ones. -/
def permitted : List Name := [`propext, `Classical.choice, `Quot.sound]

end PalomarTypeA2Axioms

run_cmd do
  let env ← getEnv
  for n in PalomarTypeA2Axioms.compared do
    match env.find? n with
    | none =>
        logError m!"MISSING declaration {n}: it is the pending stand-in for the \
theorem Palomar/comparator-type-a2.json selects, and it is not in the import \
closure of Palomar.TypeA2Solution.  Either the theorem was renamed and this \
driver was not, or this driver is checking nothing."
    | some ci =>
        logInfo m!"---- {n}\n  type: {ci.type}"
        let closure := (← collectAxioms n).qsort Name.lt
        logInfo m!"  axiom closure ({closure.size}): {closure.toList}"
        let extra := closure.toList.filter
          (fun a => !PalomarTypeA2Axioms.permitted.contains a)
        unless extra.isEmpty do
          logError m!"axiom closure of {n} leaves the permitted set: {extra}.\n\
Palomar/comparator-type-a2.json permits {PalomarTypeA2Axioms.permitted}, \
and Comparator rejects a solution whose closure exceeds it.  A `sorryAx` here \
means the translation layer is reached through an unfinished proof in the \
development, which no `sorry` scan of Palomar/TypeA2Solution.lean can see."
