import Palomar.BlanchardToeplitzSolution
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# The axiom closure of the Blanchard Question 5.4 theorem

`lake env lean scripts/PalomarBlanchardToeplitzAxioms.lean`, run by
`.github/workflows/palomar-check.yml` after the Palomar libraries build.  It
prints the axiom closure of the theorem `Palomar/comparator-blanchard-toeplitz.json`
selects and fails unless the closure lies inside the permitted axioms.  A
missing declaration fails too: a driver that cannot find its input must not
read like a driver that passed.
-/

open Lean Elab Command

namespace PalomarBlanchardToeplitzAxioms

/-- The theorem `Palomar/comparator-blanchard-toeplitz.json` selects. -/
def compared : List Name :=
  [`BlanchardToeplitz.blanchard_question_5_4]

/-- The axioms `Palomar/comparator-blanchard-toeplitz.json` permits. -/
def permitted : List Name := [`propext, `Classical.choice, `Quot.sound]

end PalomarBlanchardToeplitzAxioms

run_cmd do
  let env ← getEnv
  for n in PalomarBlanchardToeplitzAxioms.compared do
    match env.find? n with
    | none =>
        logError m!"MISSING declaration {n}: Palomar/comparator-blanchard-toeplitz.json \
selects it, and it is not in the import closure of Palomar.BlanchardToeplitzSolution.  \
Either the theorem was renamed and this driver was not, or this driver is checking \
nothing."
    | some ci =>
        logInfo m!"---- {n}\n  type: {ci.type}"
        let closure := (← collectAxioms n).qsort Name.lt
        logInfo m!"  axiom closure ({closure.size}): {closure.toList}"
        let extra := closure.toList.filter
          (fun a => !PalomarBlanchardToeplitzAxioms.permitted.contains a)
        unless extra.isEmpty do
          logError m!"axiom closure of {n} leaves the permitted set: {extra}.\n\
Palomar/comparator-blanchard-toeplitz.json permits {PalomarBlanchardToeplitzAxioms.permitted}, \
and Comparator rejects a solution whose closure exceeds it.  The incomplete-proof \
constant here means the endpoint is reached through an unfinished proof somewhere \
in the development."
