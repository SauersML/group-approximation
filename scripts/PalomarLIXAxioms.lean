import Palomar.LIXSolution
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# The axiom closure of the three compared LIX theorems

`lake env lean scripts/PalomarLIXAxioms.lean`, run by
`.github/workflows/palomar-check.yml` after the Palomar libraries build.  The
sibling driver `scripts/PalomarAxioms.lean` does the same for the one theorem
`Palomar/comparator.json` selects; this one is for the three that
`Palomar/comparator-lix.json` selects.

## Why this exists

Comparator decides a submission on three things: that each compared
declaration has the same type in both environments, that every constant those
types mention is identical in both, and that the **axiom closure of the
solution's proof** lies inside `permitted_axioms`.  This repository checked
the first two locally and not the third.
`scripts/check_palomar_submission.py` reads the two files as text,
`scripts/check_palomar_statement_match.sh` compares the compared statements as
elaborated, and `.github/workflows/palomar-comparator.yml` runs the real thing
-- but that last one is manual, takes hours, and needs a Linux runner with
Landlock.  So the cheapest of Comparator's three verdicts was the one nothing
here reproduced, and a `sorryAx` reaching an endpoint through the development
would have been discovered at submission time, after the commit is public.

`Palomar/LIXSolution.lean` containing no `sorry` is not that check.  The
closure runs through the development -- through `LIX.LIXLimit`, the LIX tower,
and the mod-2 Gysin identity `CharClass.lemmaTwoHolds` -- and the question is
what the *proof* rests on, not what one file spells.

## Why all three names

`theorem_names` may list several theorems, and Comparator checks the closure of
each.  The three LIX endpoints are not in one chain: the sharp
stage-two witness is proved first, the separable existential is derived from
it, and the negation of the printed question is derived from that.  So a driver
that checked only the last one would still be checking the closure of the
whole chain -- but the reverse is not true, and a later edit that gives one of
the three its own independent proof would leave such a driver checking
something narrower than the submission.  Reading the list, and reporting each
closure separately, is what makes the driver's verdict the submission's.

The loop deliberately does not stop at the first failure: with three
declarations, knowing that all three leave the permitted set is different
information from knowing that one does, and a run that reported only the first
would need a second run to find out.

## Why it is a driver and not `#audit_closed_axioms`

The corpus gates its own endpoints in source with `#audit_closed_axioms`, 253
times.  Putting one in `Palomar/LIXSolution.lean` would be stronger but wrong
here: `PalomarLIXSolution` is a default target, so an unexpected axiom would
fail `lake build` for every lane in a shared checkout.  A driver under
`scripts/` is not a root -- it runs under `lake env lean`, as
`scripts/ProblemXVerify.lean` and `scripts/Audit.lean` do -- so its failure is
confined to the workflow step that runs it.  The lakefile's note on the Palomar
libraries states that separation; this follows it.
-/

open Lean Elab Command

namespace PalomarLIXAxioms

/-- The declarations `Palomar/comparator-lix.json` selects, spelled as that
file spells them and in the order it lists them.  If the two ever disagree this
driver reports a missing declaration rather than passing vacuously. -/
def compared : List Name :=
  [`ProblemLIX.not_all_simple_unital_k1Injective,
   `ProblemLIX.exists_separable_simple_not_k1Injective,
   `ProblemLIX.exists_separable_simple_stage_two_witness]

/-- The axioms `Palomar/comparator-lix.json` permits, which
`scripts/check_palomar_submission.py` independently pins to exactly the three
classical ones. -/
def permitted : List Name := [`propext, `Classical.choice, `Quot.sound]

end PalomarLIXAxioms

run_cmd do
  let env ← getEnv
  for n in PalomarLIXAxioms.compared do
    match env.find? n with
    | none =>
        logError m!"MISSING declaration {n}: Palomar/comparator-lix.json \
selects it as a compared theorem, and it is not in the import closure of \
Palomar.LIXSolution.  Either the theorem was renamed and the configuration \
was not, or this driver is checking nothing."
    | some ci =>
        logInfo m!"---- {n}\n  type: {ci.type}"
        let closure := (← collectAxioms n).qsort Name.lt
        logInfo m!"  axiom closure ({closure.size}): {closure.toList}"
        let extra := closure.toList.filter
          (fun a => !PalomarLIXAxioms.permitted.contains a)
        unless extra.isEmpty do
          logError m!"axiom closure of {n} leaves the permitted set: {extra}.\n\
Palomar/comparator-lix.json permits {PalomarLIXAxioms.permitted}, and \
Comparator rejects a solution whose closure exceeds it.  A `sorryAx` here \
means the endpoint is reached through an unfinished proof in the development, \
which no `sorry` scan of Palomar/LIXSolution.lean can see."
