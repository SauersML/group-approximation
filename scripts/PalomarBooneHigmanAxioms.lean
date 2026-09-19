import Palomar.BooneHigmanSolution
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# The axiom closure of the Boone–Higman stage 1 theorems

`lake env lean scripts/PalomarBooneHigmanAxioms.lean`, modeled on
`scripts/PalomarLIXStrongAxioms.lean`. It prints the axiom closure of each theorem
`Palomar/comparator-boone-higman.json` selects and reports an error for any axiom outside the
permitted three. A `sorryAx` here means a selected statement is reached through an unfinished
proof in the development. The loop does not stop at the first failure.
-/

open Lean Elab Command

namespace PalomarBooneHigmanAxioms

/-- The theorems `Palomar/comparator-boone-higman.json` selects. -/
def compared : List Name :=
  [`BooneHigman.explicit_fp_overgroup_of_all_gl_n_q,
   `BooneHigman.kourovka_17_59,
   `BooneHigman.kohl_factorization_conjecture]

/-- The axioms `Palomar/comparator-boone-higman.json` permits. -/
def permitted : List Name := [`propext, `Classical.choice, `Quot.sound]

end PalomarBooneHigmanAxioms

run_cmd do
  let env ← getEnv
  for n in PalomarBooneHigmanAxioms.compared do
    match env.find? n with
    | none =>
        logError m!"MISSING declaration {n}: it is a theorem \
Palomar/comparator-boone-higman.json selects, and it is not in the import closure of \
Palomar.BooneHigmanSolution."
    | some ci =>
        logInfo m!"---- {n}\n  type: {ci.type}"
        let closure := (← collectAxioms n).qsort Name.lt
        logInfo m!"  axiom closure ({closure.size}): {closure.toList}"
        let extra := closure.toList.filter
          (fun a => !PalomarBooneHigmanAxioms.permitted.contains a)
        unless extra.isEmpty do
          logError m!"axiom closure of {n} leaves the permitted set: {extra}. \
Palomar/comparator-boone-higman.json permits {PalomarBooneHigmanAxioms.permitted}."
