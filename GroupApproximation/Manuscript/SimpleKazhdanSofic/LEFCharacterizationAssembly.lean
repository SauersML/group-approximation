import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFLevelEmbedding
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFRestrictedSum
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFRecursivePresentationClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:lef` and `cor:host` over the lamplighter piece alone

`simple_kazhdan_sofic_group.tex` at origin/main 696c4b602, `cor:lef` and `cor:host` (tex l.312–436).

Three pieces of `LEFCharacterization` are now proved:
* Part (i), `lefUltraproductEmbeddingStatement` (sk-lef-ultra, `LEFLevelEmbedding`);
* the restricted direct sum, `restrictedSumLEFStatement` (`LEFRestrictedSum`);
* the countably many recursive presentations, `recursivePresentationClassesStatement`
  (`LEFRecursivePresentationClasses`).

So `cor:lef` and all three statements of `cor:host` rest only on the lamplighter piece
`LEFLamplighterStatement` (tex l.384–425: the lamplighter ring `R_Δ`, `thm:general`, and
`[Δ,Δ] ≤ [Λ,Λ] ↪ G_Δ`).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

universe u

/-- **`cor:lef`** from the lamplighter piece. -/
theorem printedLEFSubgroupCharacterization_of_lamplighter (hlamp : LEFLamplighterStatement) :
    PrintedLEFSubgroupCharacterization :=
  printedLEFSubgroupCharacterization_of_pieces lefUltraproductEmbeddingStatement hlamp

/-- **The first statement of `cor:host`** from the lamplighter piece. -/
theorem printedCountableLEFHost_of_lamplighter (hlamp : LEFLamplighterStatement) :
    PrintedCountableLEFHost :=
  printedCountableLEFHost_of_pieces lefUltraproductEmbeddingStatement hlamp

/-- **The second statement of `cor:host`** from the lamplighter piece. -/
theorem printedLEFFamilyHost_of_lamplighter (hlamp : LEFLamplighterStatement) :
    PrintedLEFFamilyHost.{u} :=
  printedLEFFamilyHost_of_pieces.{u} lefUltraproductEmbeddingStatement hlamp
    restrictedSumLEFStatement

/-- **The last statement of `cor:host`** from the lamplighter piece. -/
theorem printedRecursivelyPresentedLEFHost_of_lamplighter (hlamp : LEFLamplighterStatement) :
    PrintedRecursivelyPresentedLEFHost :=
  printedRecursivelyPresentedLEFHost_of_pieces lefUltraproductEmbeddingStatement hlamp
    restrictedSumLEFStatement recursivePresentationClassesStatement

#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedLEFSubgroupCharacterization_of_lamplighter
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedCountableLEFHost_of_lamplighter
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedLEFFamilyHost_of_lamplighter
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedRecursivelyPresentedLEFHost_of_lamplighter

end SimpleKazhdanSofic
end GroupApproximation
