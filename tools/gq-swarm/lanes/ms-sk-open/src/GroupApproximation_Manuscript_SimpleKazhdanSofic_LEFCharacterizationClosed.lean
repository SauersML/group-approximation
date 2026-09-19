import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFLamplighterCombination
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterHost
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:lef` and `cor:host`: closed endpoints

`simple_kazhdan_sofic_group.tex` at origin/main 8b36733d7, section "LEF groups".

sk-lef-action's `printedLamplighterHost` (`LamplighterHost`) proves the concrete host piece
`LamplighterHostStatement` word for word: `G_Δ = EL_3(LC(Ω, F_2) ⋊ Λ)` is such a host, and `[Δ,Δ]`
embeds in it. With the pieces already proved (Part (i), the restricted direct sum and the countably
many recursive presentations), this closes:

* `printedLEFSubgroupCharacterization`: the first statement of `cor:lef`;
* `printedCountableLEFHost`, `printedLEFFamilyHost` and `printedRecursivelyPresentedLEFHost`: the
  three statements of `cor:host`. The last one covers its main clause, every recursively presented
  finitely generated LEF group; the "for instance" clauses belong to ct-involution.

The second statement of `cor:lef` rests on two pieces: `LEFSolvableWordProblemEmbeddingStatement`
(the second choice of `Δ`) and `Lamplighter.PrintedLamplighterHostSolvableWordProblem` (the word
problem of `G_Δ`). It is `printedLEFSolvableWordProblemCharacterization_of_residuals`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

universe u

/-- **The lamplighter host** (tex l.392–403): sk-lef-action's `printedLamplighterHost`, which is
`LamplighterHostStatement` word for word. -/
theorem lamplighterHostStatement : LamplighterHostStatement :=
  printedLamplighterHost

/-- **The lamplighter piece of `cor:lef` and `cor:host`**, closed. -/
theorem lefLamplighterStatement : LEFLamplighterStatement :=
  lefLamplighterStatement_of_host lamplighterHostStatement

/-- **`cor:lef`, first statement** (tex l.298–302). -/
theorem printedLEFSubgroupCharacterization : PrintedLEFSubgroupCharacterization :=
  printedLEFSubgroupCharacterization_of_host lamplighterHostStatement

/-- **`cor:host`, first statement** (tex l.308): every countable LEF group is a subgroup of such a
group. -/
theorem printedCountableLEFHost : PrintedCountableLEFHost :=
  printedCountableLEFHost_of_lamplighter lefLamplighterStatement

/-- **`cor:host`, second statement** (tex l.309–310). -/
theorem printedLEFFamilyHost : PrintedLEFFamilyHost.{u} :=
  printedLEFFamilyHost_of_lamplighter.{u} lefLamplighterStatement

/-- **`cor:host`, last statement, main clause** (tex l.310–312): one such group contains every
recursively presented finitely generated LEF group. -/
theorem printedRecursivelyPresentedLEFHost : PrintedRecursivelyPresentedLEFHost :=
  printedRecursivelyPresentedLEFHost_of_lamplighter lefLamplighterStatement

/-- **`cor:lef`, second statement** (tex l.303–304), over the second choice of `Δ` and the word
problem of `G_Δ`. -/
theorem printedLEFSolvableWordProblemCharacterization_of_residuals
    (hultra : LEFSolvableWordProblemEmbeddingStatement)
    (hswp : Lamplighter.PrintedLamplighterHostSolvableWordProblem) :
    PrintedLEFSolvableWordProblemCharacterization :=
  printedLEFSolvableWordProblemCharacterization_of_lamplighter hultra lamplighterHostStatement hswp

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.lamplighterHostStatement
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.lefLamplighterStatement
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedLEFSubgroupCharacterization
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedCountableLEFHost
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedLEFFamilyHost
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedRecursivelyPresentedLEFHost
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedLEFSolvableWordProblemCharacterization_of_residuals

end SimpleKazhdanSofic
end GroupApproximation
