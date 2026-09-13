import Palomar.TypeA2Solution
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# The axiom closure of the FFWZ Question 5.8 theorem

`lake env lean scripts/PalomarTypeA2Axioms.lean`, run by
`.github/workflows/palomar-check.yml` after the Palomar libraries build.  It
prints the axiom closure of the theorem `Palomar/comparator-type-a2.json`
selects and fails unless that closure lies inside the permitted axioms.  A
missing declaration fails too: a driver that cannot find its input must not
read like a driver that passed.
-/

open Lean Elab Command

namespace PalomarTypeA2Axioms

/-- The theorem `Palomar/comparator-type-a2.json` selects. -/
def compared : List Name :=
  [`FFWZ.exists_isTypeA2_quotient_not_isFinitelyPresented]

/-- The axioms `Palomar/comparator-type-a2.json` permits. -/
def permitted : List Name := [`propext, `Classical.choice, `Quot.sound]

end PalomarTypeA2Axioms

run_cmd do
  let env ← getEnv
  for n in PalomarTypeA2Axioms.compared do
    match env.find? n with
    | none =>
        logError m!"MISSING declaration {n}: Palomar/comparator-type-a2.json \
selects it, and it is not in the import closure of Palomar.TypeA2Solution.  \
Either the theorem was renamed and this driver was not, or this driver is checking \
nothing."
    | some ci =>
        logInfo m!"---- {n}\n  type: {ci.type}"
        let closure := (← collectAxioms n).qsort Name.lt
        logInfo m!"  axiom closure ({closure.size}): {closure.toList}"
        let extra := closure.toList.filter
          (fun a => !PalomarTypeA2Axioms.permitted.contains a)
        unless extra.isEmpty do
          logError m!"axiom closure of {n} leaves the permitted set: {extra}.\n\
Palomar/comparator-type-a2.json permits {PalomarTypeA2Axioms.permitted}, \
and Comparator rejects a solution whose closure exceeds it.  The incomplete-proof \
constant here means the endpoint is reached through an unfinished proof somewhere \
in the development."
