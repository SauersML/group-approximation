import Palomar.GubaThompsonSolution
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# The axiom closure of the Guba Question 3.20 theorems

`lake env lean scripts/PalomarGubaThompsonAxioms.lean`, run by
`.github/workflows/palomar-check.yml` after the Palomar libraries build.  The
siblings `scripts/PalomarPestov91Axioms.lean` and
`scripts/PalomarTypeA2Axioms.lean` do the same for two other pending
configurations.

## Why this one gates although its configuration is pending

`Palomar/comparator-guba-thompson.json` is not submittable yet.  Its solution
derives each selected statement from three facts about Thompson's group `F`
that the development does not yet prove on `F`: `K[F]` has no zero divisors,
Guba's Theorem 3.18 holds for `x₀`, and `x₁` lies in a subgroup `H` with an
isomorphism `H ≃* F` sending `x₁` to `x₀`, which contains or is contained in
each of its conjugates.  So the challenge and solution signatures do not match
and `scripts/check_palomar_submission.py` lists the configuration as pending.

The `_of` forms are sorry-free: the outstanding facts are hypotheses, not holes.
So a `sorryAx` reaching them through the translation layer of
`Palomar/GubaThompsonSolution.lean` is a real defect today, and no `sorry` scan
of that file can see it.

## Why the names carry `_of`

The configuration selects `GubaThompson.question_3_20` and
`GubaThompson.question_3_20_common_multiple`, and the solution does not declare
those names yet.  What it declares is each of them with the outstanding facts
in front, under the name with `_of` appended.  When those facts are proved on
`F`, the solution gains the two unsuffixed theorems and the list below is
rewritten to the configuration's names, in the same change that moves the
configuration to `PALOMAR_CONFIGS`.

The loop does not stop at the first failure: knowing that both theorems leave
the permitted set is different information from knowing that one does.
-/

open Lean Elab Command

namespace PalomarGubaThompsonAxioms

/-- The declarations that stand in, while the configuration is pending, for the
two `Palomar/comparator-guba-thompson.json` selects: each of them with the
outstanding facts about `F` as leading hypotheses. -/
def compared : List Name :=
  [`GubaThompson.question_3_20_of,
   `GubaThompson.question_3_20_common_multiple_of]

/-- The axioms `Palomar/comparator-guba-thompson.json` permits, which
`scripts/check_palomar_submission.py` independently pins to exactly the three
classical ones. -/
def permitted : List Name := [`propext, `Classical.choice, `Quot.sound]

end PalomarGubaThompsonAxioms

run_cmd do
  let env ← getEnv
  for n in PalomarGubaThompsonAxioms.compared do
    match env.find? n with
    | none =>
        logError m!"MISSING declaration {n}: it is the pending stand-in for a \
theorem Palomar/comparator-guba-thompson.json selects, and it is not in the \
import closure of Palomar.GubaThompsonSolution.  Either the theorem was renamed \
and this driver was not, or this driver is checking nothing."
    | some ci =>
        logInfo m!"---- {n}\n  type: {ci.type}"
        let closure := (← collectAxioms n).qsort Name.lt
        logInfo m!"  axiom closure ({closure.size}): {closure.toList}"
        let extra := closure.toList.filter
          (fun a => !PalomarGubaThompsonAxioms.permitted.contains a)
        unless extra.isEmpty do
          logError m!"axiom closure of {n} leaves the permitted set: {extra}.\n\
Palomar/comparator-guba-thompson.json permits \
{PalomarGubaThompsonAxioms.permitted}, and Comparator rejects a solution whose \
closure exceeds it.  A `sorryAx` here means the translation layer is reached \
through an unfinished proof in the development, which no `sorry` scan of \
Palomar/GubaThompsonSolution.lean can see."
