import Palomar.SurjunctiveNonsoficSolution
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# The axiom closure of the surjunctive nonsofic group theorems

`lake env lean scripts/PalomarSurjunctiveNonsoficAxioms.lean`, run by
`.github/workflows/palomar-check.yml` after the Palomar libraries build.  It
prints the axiom closure of each theorem `Palomar/comparator-surjunctive-nonsofic.json`
selects and fails unless every closure lies inside the permitted axioms.  A
missing declaration fails too: a driver that cannot find its input must not
read like a driver that passed.

The loop does not stop at the first failure: knowing that both theorems leave
the permitted set is different information from knowing that one does.
-/

open Lean Elab Command

namespace PalomarSurjunctiveNonsoficAxioms

/-- The theorems `Palomar/comparator-surjunctive-nonsofic.json` selects. -/
def compared : List Name :=
  [`SurjunctiveNonsofic.not_all_surjunctive_groups_sofic,
   `SurjunctiveNonsofic.exists_finitelyGenerated_surjunctive_not_sofic]

/-- The axioms `Palomar/comparator-surjunctive-nonsofic.json` permits. -/
def permitted : List Name := [`propext, `Classical.choice, `Quot.sound]

end PalomarSurjunctiveNonsoficAxioms

run_cmd do
  let env ← getEnv
  for n in PalomarSurjunctiveNonsoficAxioms.compared do
    match env.find? n with
    | none =>
        logError m!"MISSING declaration {n}: Palomar/comparator-surjunctive-nonsofic.json \
selects it, and it is not in the import closure of Palomar.SurjunctiveNonsoficSolution.  \
Either the theorem was renamed and this driver was not, or this driver is checking \
nothing."
    | some ci =>
        logInfo m!"---- {n}\n  type: {ci.type}"
        let closure := (← collectAxioms n).qsort Name.lt
        logInfo m!"  axiom closure ({closure.size}): {closure.toList}"
        let extra := closure.toList.filter
          (fun a => !PalomarSurjunctiveNonsoficAxioms.permitted.contains a)
        unless extra.isEmpty do
          logError m!"axiom closure of {n} leaves the permitted set: {extra}.\n\
Palomar/comparator-surjunctive-nonsofic.json permits {PalomarSurjunctiveNonsoficAxioms.permitted}, \
and Comparator rejects a solution whose closure exceeds it.  The incomplete-proof \
constant here means the endpoint is reached through an unfinished proof somewhere \
in the development."
