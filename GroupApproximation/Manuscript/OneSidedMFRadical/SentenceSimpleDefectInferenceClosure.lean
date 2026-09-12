import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveConfiguration
import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveSimplicity

/-!
# The exact simplicity inference in the rank-twelve defect argument

Sentence-level closure for census rows 67--68.  The existing full-radical
endpoint uses an independently stronger normal-generation theorem.  This file
instead records the manuscript's printed inference itself: in a simple group,
a normal subgroup containing a nonidentity element is the whole group.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open RankTwelveEndpoint

section SimpleInference

variable {G : Type*} [Group G]

/-- A normal subgroup of a simple group which contains a nonidentity element
is the whole group.  This is the exact abstract inference used in sentences
67 and 68. -/
theorem top_le_normal_of_simple_of_nontrivial_mem
    (hG : IsSimpleGroup G) (N : Subgroup G) (hN : N.Normal)
    {d : G} (hd : d ≠ 1) (hdN : d ∈ N) :
    (⊤ : Subgroup G) ≤ N := by
  rcases hG.eq_bot_or_eq_top_of_normal N hN with hbot | htop
  · exfalso
    exact hd (Subgroup.mem_bot.mp (hbot ▸ hdN))
  · exact htop.ge

end SimpleInference

/-- **Sentence 67.**  The printed nonidentity defect normally generates the
rank-twelve group, deduced here specifically from the separately proved
simplicity theorem. -/
theorem manuscriptSentence67_simplicity_gives_defect_normalGeneration :
    Subgroup.normalClosure ({defect} : Set H) = ⊤ := by
  apply top_unique
  exact top_le_normal_of_simple_of_nontrivial_mem
    manuscriptPropositionSimple
    (Subgroup.normalClosure ({defect} : Set H))
    Subgroup.normalClosure_normal defect_ne_one
    (Subgroup.subset_normalClosure (Set.mem_singleton defect))

/-- **Sentence 68.**  The displayed commutator puts `d` in the printed
defect; simplicity and `d ≠ 1` then make that normal defect the whole ambient
group.  This proof deliberately does not invoke the independent theorem that
`d` normally generates by elementary-root calculus. -/
theorem manuscriptSentence68_simplicity_saturates_printedDefect :
    defect ∈ printedDefect corner ∧
      (⊤ : Subgroup H) ≤ printedDefect corner ∧
      printedDefect corner = ⊤ := by
  have hdD : defect ∈ printedDefect corner := by
    rw [← tau_c_commutator_ell]
    exact printedDefect_generator_mem corner tau_compresses_corner
      c_commutes_corner ell_mem_corner
  have htop : (⊤ : Subgroup H) ≤ printedDefect corner :=
    top_le_normal_of_simple_of_nontrivial_mem manuscriptPropositionSimple
      (printedDefect corner) (printedDefect_normal corner) defect_ne_one hdD
  exact ⟨hdD, htop, top_le_iff.mp htop⟩

end OneSidedMFRadical
end Manuscript
end GroupApproximation
