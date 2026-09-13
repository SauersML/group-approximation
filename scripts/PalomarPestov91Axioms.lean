import Palomar.Pestov91Solution
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# The axiom closure of the Pestov Open Question 9.1 theorems

`lake env lean scripts/PalomarPestov91Axioms.lean`, run by
`.github/workflows/palomar-check.yml` after the Palomar libraries build.  The
siblings `scripts/PalomarLIXStrongAxioms.lean` and
`scripts/PalomarBowenChapmanAxioms.lean` do the same for two other
configurations.

## Why this one gates although its configuration is pending

`Palomar/comparator-pestov91.json` is not submittable yet.  Its solution derives
each selected statement from the existence of an infinite simple LEF group with
property (T), which the development still owes, so the challenge and solution
signatures do not match and `scripts/check_palomar_submission.py` lists the
configuration as pending.

The `_of` forms are sorry-free: the outstanding existence statement is a
hypothesis, not a hole.  So a `sorryAx` reaching them through the translation
layer of `Palomar/Pestov91Solution.lean` is a real defect today, and no `sorry`
scan of that file can see it.

## Why the names carry `_of`

The configuration selects `Pestov91.exists_infinite_simple_propertyT_hyperlinear`
and `Pestov91.exists_infinite_simple_propertyT_sofic`, and the solution does not
declare those names yet.  What it declares is each of them with the outstanding
existence statement in front, under the name with `_of` appended.  When the
witness lands, the solution gains the two unsuffixed theorems and the list below
is rewritten to the configuration's names, in the same change that moves the
configuration to `PALOMAR_CONFIGS`.

The loop does not stop at the first failure: knowing that both theorems leave
the permitted set is different information from knowing that one does.
-/

open Lean Elab Command

namespace PalomarPestov91Axioms

/-- The declarations that stand in, while the configuration is pending, for the
two `Palomar/comparator-pestov91.json` selects: each of them with the one
outstanding existence statement as a leading hypothesis. -/
def compared : List Name :=
  [`Pestov91.exists_infinite_simple_propertyT_hyperlinear_of,
   `Pestov91.exists_infinite_simple_propertyT_sofic_of]

/-- The axioms `Palomar/comparator-pestov91.json` permits, which
`scripts/check_palomar_submission.py` independently pins to exactly the three
classical ones. -/
def permitted : List Name := [`propext, `Classical.choice, `Quot.sound]

end PalomarPestov91Axioms

run_cmd do
  let env ← getEnv
  for n in PalomarPestov91Axioms.compared do
    match env.find? n with
    | none =>
        logError m!"MISSING declaration {n}: it is the pending stand-in for a \
theorem Palomar/comparator-pestov91.json selects, and it is not in the import \
closure of Palomar.Pestov91Solution.  Either the theorem was renamed and this \
driver was not, or this driver is checking nothing."
    | some ci =>
        logInfo m!"---- {n}\n  type: {ci.type}"
        let closure := (← collectAxioms n).qsort Name.lt
        logInfo m!"  axiom closure ({closure.size}): {closure.toList}"
        let extra := closure.toList.filter
          (fun a => !PalomarPestov91Axioms.permitted.contains a)
        unless extra.isEmpty do
          logError m!"axiom closure of {n} leaves the permitted set: {extra}.\n\
Palomar/comparator-pestov91.json permits {PalomarPestov91Axioms.permitted}, \
and Comparator rejects a solution whose closure exceeds it.  A `sorryAx` here \
means the translation layer is reached through an unfinished proof in the \
development, which no `sorry` scan of Palomar/Pestov91Solution.lean can see."
