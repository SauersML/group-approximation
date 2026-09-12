import Palomar.LIXStrongSolution
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# The axiom closure of the three strengthened LIX theorems

`lake env lean scripts/PalomarLIXStrongAxioms.lean`, run by
`.github/workflows/palomar-check.yml` after the Palomar libraries build.  The
siblings `scripts/PalomarAxioms.lean` and `scripts/PalomarLIXAxioms.lean` do
the same for the other two configurations.

## Why this one gates although its configuration is pending

`Palomar/comparator-lix-strong.json` is not submittable: its solution proves
each selected statement from one proposition the construction still owes, so
the challenge and solution signatures do not match and
`scripts/check_palomar_submission.py` lists the configuration as pending.

The axiom closure is the one of Comparator's three verdicts that does not care
about that.  The `_of` forms are **sorry-free** -- their outstanding
proposition is a hypothesis, not a hole -- so the closure they rest on is
already the closure the finished theorems will rest on, minus nothing.  A
`sorryAx` appearing here would mean the strengthened endpoint is reached
through an unfinished proof somewhere in the development, which is exactly what
this driver is for and which no `sorry` scan of `Palomar/LIXStrongSolution.lean`
can see.  So the check is meaningful from the first day and is not deferred.

## Why the names carry `_of`

`Palomar/comparator-lix-strong.json` selects
`ProblemLIXStrong.exists_simple_separable_powers_outside_U0` and its two
siblings, and those names do not exist yet.  What exists is each of them with
`GroupApproximation.NinetyNineProblems.ClimbedPowersOutside` in front, under the
name with `_of` appended.  Naming those here rather than the configuration's
names is the difference between a driver that reports a missing declaration
every run and one that checks something.  When the proposition lands, the
solution gains the three unsuffixed theorems and the list below is rewritten to
the configuration's names, in the same change that moves the configuration to
`PALOMAR_CONFIGS`.

The loop deliberately does not stop at the first failure: knowing that all
three leave the permitted set is different information from knowing that one
does.
-/

open Lean Elab Command

namespace PalomarLIXStrongAxioms

/-- The declarations that stand in, while the configuration is pending, for the
three `Palomar/comparator-lix-strong.json` selects: each of them with the one
outstanding proposition as a leading hypothesis. -/
def compared : List Name :=
  [`ProblemLIXStrong.exists_simple_separable_powers_outside_U0_of,
   `ProblemLIXStrong.exists_simple_separable_order_six_witness_of,
   `ProblemLIXStrong.exists_simple_separable_squarefree_witness_of]

/-- The axioms `Palomar/comparator-lix-strong.json` permits, which
`scripts/check_palomar_submission.py` independently pins to exactly the three
classical ones. -/
def permitted : List Name := [`propext, `Classical.choice, `Quot.sound]

end PalomarLIXStrongAxioms

run_cmd do
  let env ← getEnv
  for n in PalomarLIXStrongAxioms.compared do
    match env.find? n with
    | none =>
        logError m!"MISSING declaration {n}: it is the pending stand-in for a \
theorem Palomar/comparator-lix-strong.json selects, and it is not in the import \
closure of Palomar.LIXStrongSolution.  Either the theorem was renamed and this \
driver was not, or this driver is checking nothing."
    | some ci =>
        logInfo m!"---- {n}\n  type: {ci.type}"
        let closure := (← collectAxioms n).qsort Name.lt
        logInfo m!"  axiom closure ({closure.size}): {closure.toList}"
        let extra := closure.toList.filter
          (fun a => !PalomarLIXStrongAxioms.permitted.contains a)
        unless extra.isEmpty do
          logError m!"axiom closure of {n} leaves the permitted set: {extra}.\n\
Palomar/comparator-lix-strong.json permits {PalomarLIXStrongAxioms.permitted}, \
and Comparator rejects a solution whose closure exceeds it.  A `sorryAx` here \
means the strengthened endpoint is reached through an unfinished proof in the \
development, which no `sorry` scan of Palomar/LIXStrongSolution.lean can see."
