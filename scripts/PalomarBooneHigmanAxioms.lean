import Palomar.BooneHigmanSolution
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# The axiom closure of the Boone–Higman megasubmission theorems

`lake env lean scripts/PalomarBooneHigmanAxioms.lean`, modeled on
`scripts/PalomarLIXStrongAxioms.lean`. `Palomar/comparator-boone-higman.json` is pending, but
the `_of` forms are sorry-free (their outstanding propositions are hypotheses, not holes), so
their axiom closure is already the closure the finished theorems will rest on. A `sorryAx`
here means a selected statement is reached through an unfinished proof in the development.

The names carry `_of` because the configuration's unsuffixed names do not exist yet. The loop
does not stop at the first failure.
-/

open Lean Elab Command

namespace PalomarBooneHigmanAxioms

/-- The declarations that stand in, while the configuration is pending, for the theorems
`Palomar/comparator-boone-higman.json` selects. -/
def compared : List Name :=
  [`BooneHigman.explicit_fp_overgroup_of_all_gl_n_q_of,
   `BooneHigman.finitely_presented_metabelian_embeds_in_finitely_presented_simple_of,
   `BooneHigman.finitely_generated_metabelian_embeds_in_finitely_presented_simple_of,
   `BooneHigman.finitely_generated_linear_embeds_in_finitely_presented_simple_of,
   `BooneHigman.finitely_generated_linear_embeds_in_finitely_presented_self_similar_of,
   `BooneHigman.kourovka_17_57_of,
   `BooneHigman.kourovka_17_59_of,
   `BooneHigman.kourovka_17_61_of,
   `BooneHigman.graph_product_embeds_in_type_a_group_of,
   `BooneHigman.exists_fp_simple_with_mixed_identities_not_finitely_normally_generated_of]

/-- The axioms `Palomar/comparator-boone-higman.json` permits. -/
def permitted : List Name := [`propext, `Classical.choice, `Quot.sound]

end PalomarBooneHigmanAxioms

run_cmd do
  let env ← getEnv
  for n in PalomarBooneHigmanAxioms.compared do
    match env.find? n with
    | none =>
        logError m!"MISSING declaration {n}: it stands in for a theorem \
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
