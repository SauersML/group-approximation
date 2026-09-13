import Palomar.GKPCommutingActionsSolution
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# The axiom closure of the GKP Question 4.2 theorems

`lake env lean scripts/PalomarGKPCommutingActionsAxioms.lean`, run by
`.github/workflows/palomar-check.yml` after the Palomar libraries build.  It
prints the axiom closure of each theorem
`Palomar/comparator-gkp-commuting-actions.json` selects and fails unless every
closure lies inside the permitted axioms.  A missing declaration fails too: a
driver that cannot find its input must not read like a driver that passed.

The loop does not stop at the first failure: knowing that both theorems leave
the permitted set is different information from knowing that one does.
-/

open Lean Elab Command

namespace PalomarGKPCommutingActionsAxioms

/-- The theorems `Palomar/comparator-gkp-commuting-actions.json` selects. -/
def compared : List Name :=
  [`GKPCommutingActions.commuting_sofic_actions_need_not_combine,
   `GKPCommutingActions.exists_commuting_sofic_actions_not_sofic]

/-- The axioms `Palomar/comparator-gkp-commuting-actions.json` permits. -/
def permitted : List Name := [`propext, `Classical.choice, `Quot.sound]

end PalomarGKPCommutingActionsAxioms

run_cmd do
  let env ← getEnv
  for n in PalomarGKPCommutingActionsAxioms.compared do
    match env.find? n with
    | none =>
        logError m!"MISSING declaration {n}: Palomar/comparator-gkp-commuting-actions.json \
selects it, and it is not in the import closure of Palomar.GKPCommutingActionsSolution.  \
Either the theorem was renamed and this driver was not, or this driver is checking \
nothing."
    | some ci =>
        logInfo m!"---- {n}\n  type: {ci.type}"
        let closure := (← collectAxioms n).qsort Name.lt
        logInfo m!"  axiom closure ({closure.size}): {closure.toList}"
        let extra := closure.toList.filter
          (fun a => !PalomarGKPCommutingActionsAxioms.permitted.contains a)
        unless extra.isEmpty do
          logError m!"axiom closure of {n} leaves the permitted set: {extra}.\n\
Palomar/comparator-gkp-commuting-actions.json permits \
{PalomarGKPCommutingActionsAxioms.permitted}, and Comparator rejects a solution whose \
closure exceeds it.  The incomplete-proof constant here means the endpoint is reached \
through an unfinished proof somewhere in the development."
