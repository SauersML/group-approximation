import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCharacterizationClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFSecondDelta
import GroupApproximation.Meta.AxiomGuard

/-!
# The second statement of `cor:lef` over the word problem of `G_Δ` alone

`simple_kazhdan_sofic_group.tex` at origin/main 8b36733d7, `cor:lef`, second statement
(tex l.303–304):

> It is LEF with solvable word problem if and only if it is a subgroup of such a group with
> solvable word problem.

sk-lef-ultra's `lefSolvableWordProblemEmbeddingStatement` (`LEFSecondDelta`) proves the second
choice of `Δ`, and sk-lef-action's `printedLamplighterHost` proves the host. So the second statement
rests only on `Lamplighter.PrintedLamplighterHostSolvableWordProblem`: `G_Δ` has solvable word
problem whenever `Δ` does (tex l.447–455).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

/-- **`cor:lef`, second statement** (tex l.303–304), over the word problem of `G_Δ`. -/
theorem printedLEFSolvableWordProblemCharacterization_of_hostWordProblem
    (hswp : Lamplighter.PrintedLamplighterHostSolvableWordProblem) :
    PrintedLEFSolvableWordProblemCharacterization :=
  printedLEFSolvableWordProblemCharacterization_of_residuals lefSolvableWordProblemEmbeddingStatement
    hswp

#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedLEFSolvableWordProblemCharacterization_of_hostWordProblem

end SimpleKazhdanSofic
end GroupApproximation
