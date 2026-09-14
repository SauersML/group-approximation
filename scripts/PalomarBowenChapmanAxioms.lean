import Palomar.BowenChapmanSolution
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# The axiom closure of the Bowen–Chapman Problem 1.1 theorems

`lake env lean scripts/PalomarBowenChapmanAxioms.lean`, run by
`.github/workflows/palomar-check.yml` after the Palomar libraries build.  The
siblings `scripts/PalomarLIXAxioms.lean` and `scripts/PalomarLIXStrongAxioms.lean`
do the same for the other configurations.

## Why this one gates although its configuration is pending

`Palomar/comparator-bowen-chapman.json` is not submittable yet: its solution
proves each selected statement from the development endpoint's statement,
which is not in the solution's import closure yet, so
`scripts/check_palomar_submission.py` lists the configuration as pending.

The `_of` forms carry that statement as a hypothesis, not as a hole, so the
closure they rest on is the closure of the bridging steps, and it must already
be exactly the three classical axioms.  Anything else here is a real defect
today.

## Why the names carry `_of`

The configuration selects `BowenChapman.not_all_surjunctive_groups_sofic` and
`BowenChapman.exists_finitelyGenerated_surjunctive_not_sofic`, and those names
do not exist in the solution yet.  When the endpoint lands, the solution gains
the two unsuffixed theorems and the list below is rewritten to the
configuration's names, in the same change that moves the configuration to
`PALOMAR_CONFIGS`.

The loop does not stop at the first failure: knowing that both leave the
permitted set is different information from knowing that one does.
-/

open Lean Elab Command

namespace PalomarBowenChapmanAxioms

/-- The declarations that stand in, while the configuration is pending, for the
two `Palomar/comparator-bowen-chapman.json` selects: each of them with the
endpoint statement as a leading hypothesis. -/
def compared : List Name :=
  [`BowenChapman.not_all_surjunctive_groups_sofic_of,
   `BowenChapman.exists_finitelyGenerated_surjunctive_not_sofic_of]

/-- The axioms `Palomar/comparator-bowen-chapman.json` permits. -/
def permitted : List Name := [`propext, `Classical.choice, `Quot.sound]

end PalomarBowenChapmanAxioms

run_cmd do
  let env ← getEnv
  for n in PalomarBowenChapmanAxioms.compared do
    match env.find? n with
    | none =>
        logError m!"MISSING declaration {n}: it is the pending stand-in for a \
theorem Palomar/comparator-bowen-chapman.json selects, and it is not in the import \
closure of Palomar.BowenChapmanSolution.  Either the theorem was renamed and this \
driver was not, or this driver is checking nothing."
    | some ci =>
        logInfo m!"---- {n}\n  type: {ci.type}"
        let closure := (← collectAxioms n).qsort Name.lt
        logInfo m!"  axiom closure ({closure.size}): {closure.toList}"
        let extra := closure.toList.filter
          (fun a => !PalomarBowenChapmanAxioms.permitted.contains a)
        unless extra.isEmpty do
          logError m!"axiom closure of {n} leaves the permitted set: {extra}.\n\
Palomar/comparator-bowen-chapman.json permits {PalomarBowenChapmanAxioms.permitted}, \
and Comparator rejects a solution whose closure exceeds it.  The incomplete-proof \
constant here means the bridge is reached through an unfinished proof somewhere \
in the development."
