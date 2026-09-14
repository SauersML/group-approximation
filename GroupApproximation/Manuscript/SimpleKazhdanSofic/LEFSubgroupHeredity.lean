import GroupApproximation.Sofic.LEF
import GroupApproximation.Meta.AxiomGuard

/-!
# LEF passes to subgroups

`simple_kazhdan_sofic_group.tex` at origin/main 8b36733d7, proof of `cor:lef`, second statement
(tex l.455–457):

> Conversely, finitely generated subgroups of groups with solvable word problem have solvable word
> problem, and LEF passes to subgroups.

The solvable word problem clause is `printedSolvableWordProblemHeredity`
(`LEFSolvableWordProblem`). This module names the LEF clause as a closed endpoint, through
`isLEF_of_injective`, with "subgroup" read as an injective homomorphism.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

/-- **LEF passes to subgroups** (tex l.456–457): a group that embeds in an LEF group is LEF. -/
def PrintedSubgroupsOfLEFAreLEF : Prop :=
  ∀ (H G : Type) [Group H] [Group G] (f : H →* G), Function.Injective f → IsLEF G → IsLEF H

theorem printedSubgroupsOfLEFAreLEF : PrintedSubgroupsOfLEFAreLEF :=
  fun _ _ _ _ f hf hG => isLEF_of_injective f hf hG

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedSubgroupsOfLEFAreLEF

end SimpleKazhdanSofic
end GroupApproximation
