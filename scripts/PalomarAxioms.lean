import Palomar.Solution
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# The axiom closure of the compared theorem

`lake env lean scripts/PalomarAxioms.lean`, run by
`.github/workflows/palomar-check.yml` after the Palomar libraries build.

## Why this exists

Comparator decides a submission on three things: that the compared
declaration has the same type in both environments, that every constant that
type mentions is identical in both, and that the **axiom closure of the
solution's proof** lies inside `permitted_axioms`.  This repository checked
the first two locally and not the third.
`scripts/check_palomar_submission.py` reads the two files as text,
`scripts/check_palomar_statement_match.sh` compares the compared statement as
elaborated, and `.github/workflows/palomar-comparator.yml` runs the real thing
-- but that last one is manual, takes hours, and needs a Linux runner with
Landlock.  So the cheapest of Comparator's three verdicts was the one nothing
here reproduced, and a `sorryAx` reaching the endpoint through the development
would have been discovered at submission time, after the commit is public.

`Palomar/Solution.lean` containing no `sorry` is not that check.  The closure
runs through the development, and the question is what the *proof* rests on,
not what one file spells.

## Why it is a driver and not `#audit_closed_axioms`

The corpus gates its own endpoints in source with `#audit_closed_axioms`, 253
times.  Putting one in `Palomar/Solution.lean` would be stronger but wrong
here: `PalomarSolution` is a default target, so an unexpected axiom would fail
`lake build` for every lane in a shared checkout.  A driver under `scripts/`
is not a root -- it runs under `lake env lean`, as `scripts/ProblemXVerify.lean`
and `scripts/Audit.lean` do -- so its failure is confined to the workflow step
that runs it.  The lakefile's note on the Palomar libraries states that
separation; this follows it.

The shape is borrowed from `tristanbuckmaster/fluid_lean`'s
`scripts/PrintAxioms.lean`, which is `import Solution` plus two
`#print axioms` lines.  That prints and does not decide; this compares against
the permitted set and fails, and it reads the name from one place so that a
rename cannot leave it silently checking nothing.
-/

open Lean Elab Command

namespace PalomarAxioms

/-- The declaration `Palomar/comparator.json` selects, spelled as that file
spells it.  If the two ever disagree this driver reports a missing
declaration rather than passing vacuously. -/
def compared : Name := `ExplicitNonMF.explicit_sofic_not_MF

/-- The axioms `Palomar/comparator.json` permits, which
`scripts/check_palomar_submission.py` independently pins to exactly the three
classical ones. -/
def permitted : List Name := [`propext, `Classical.choice, `Quot.sound]

end PalomarAxioms

run_cmd do
  let env ← getEnv
  let n := PalomarAxioms.compared
  match env.find? n with
  | none =>
      logError m!"MISSING declaration {n}: Palomar/comparator.json selects it \
as the compared theorem, and it is not in the import closure of \
Palomar.Solution.  Either the theorem was renamed and the configuration was \
not, or this driver is checking nothing."
  | some ci =>
      logInfo m!"---- {n}\n  type: {ci.type}"
      let closure := (← collectAxioms n).qsort Name.lt
      logInfo m!"  axiom closure ({closure.size}): {closure.toList}"
      let extra := closure.toList.filter
        (fun a => !PalomarAxioms.permitted.contains a)
      unless extra.isEmpty do
        logError m!"axiom closure of {n} leaves the permitted set: {extra}.\n\
Palomar/comparator.json permits {PalomarAxioms.permitted}, and Comparator \
rejects a solution whose closure exceeds it.  A `sorryAx` here means the \
endpoint is reached through an unfinished proof in the development, which no \
`sorry` scan of Palomar/Solution.lean can see."
