import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveSimplicity
import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceDefectCalculationProofClosure
import GroupApproximation.Manuscript.OneSidedMFRadical.ReducedCStarConsequence
import GroupApproximation.Meta.AxiomGuard

/-!
# Sentence-level closure of the headline proof path

This module retains the intermediate subgroup inclusions used in the printed
proof.  In particular, saturation of the defect is not represented merely by
its endpoint: normality, containment of the normal closure, normal generation,
and the final equality are separate declarations.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RankTwelveEndpoint

open scoped commutatorElement

local instance manuscriptHeadlineCountable : Countable H := countable
local instance manuscriptHeadlineNontrivial : Nontrivial H := nontrivial

/-- Compression and centrality put the displayed commutator in the printed
defect subgroup. -/
theorem manuscriptExplicitDefect_mem_printedDefect :
    defect ∈ printedDefect corner := by
  rw [← manuscriptMovedMark_defectCalculation]
  exact printedDefect_generator_mem corner tau_compresses_corner
    c_commutes_corner ell_mem_corner

/-- The printed defect subgroup is normal. -/
theorem manuscriptPrintedDefect_normal : (printedDefect corner).Normal :=
  inferInstance

/-- Normality and membership of `d` force the normal closure of `d` into the
printed defect subgroup. -/
theorem manuscriptNormalClosureDefect_le_printedDefect :
    Subgroup.normalClosure ({defect} : Set H) ≤ printedDefect corner := by
  apply Subgroup.normalClosure_le_normal
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  simpa [hx] using manuscriptExplicitDefect_mem_printedDefect

/-- Since the displayed defect normally generates `H`, the printed defect is
all of `H`. -/
theorem manuscriptPrintedDefect_eq_top_from_normalGeneration :
    printedDefect corner = ⊤ := by
  apply top_unique
  rw [← manuscriptDefectNormallyGenerates_from_printedSandwich]
  exact manuscriptNormalClosureDefect_le_printedDefect

/-- Applying the one-sided compression criterion with the ambient Kazhdan
subgroup `K=H` gives the literal manuscript MF radical. -/
theorem manuscriptRadical_eq_top_from_criterion_with_K_eq_H :
    manuscriptCoronaMFResidual H = ⊤ :=
  (manuscriptOneSidedCompressionCriterion (G := H) corner
      corner_hasKazhdanPropertyT).2.2
    hasKazhdanPropertyT manuscriptPrintedDefect_eq_top_from_normalGeneration

/-- The basis-free and literal corona readings agree, so the actual corona MF
radical is also all of `H`. -/
theorem manuscriptActualRadical_eq_top_from_literalRadical :
    actualCoronaMFResidual H = ⊤ := by
  rw [← manuscriptCoronaMFResidual_eq_actualCoronaMFResidual]
  exact manuscriptRadical_eq_top_from_criterion_with_K_eq_H

/-- The simplicity assertion is independent of the preceding radical
calculation. -/
theorem manuscriptNontrivial_and_simple_independently :
    Nontrivial H ∧ IsSimpleGroup H :=
  ⟨nontrivial, manuscriptPropositionSimple⟩

/-- A full radical kills every homomorphism into a countable MF target. -/
theorem manuscriptEveryMapToMF_is_trivial
    (M : Type) [Group M] [Countable M] (hM : IsCDEOperatorMF M)
    (f : H →* M) (x : H) :
    f x = 1 :=
  manuscriptFullRadicalKillsMFTargets
    (G := H) (M := M)
    manuscriptRadical_eq_top_from_criterion_with_K_eq_H
    ((isCDEOperatorMF_iff_isOperatorMF M).mp hM) f x

/-- Applying the preceding statement to the identity map rules out MF-ness of
`H`. -/
theorem manuscriptIdentityMap_contradicts_MF : ¬ IsCDEOperatorMF H := by
  intro hMF
  obtain ⟨x, hx⟩ := exists_ne (1 : H)
  have hid := manuscriptEveryMapToMF_is_trivial H hMF (MonoidHom.id H) x
  exact hx (by simpa using hid)

#audit_closed_axioms manuscriptExplicitDefect_mem_printedDefect
#audit_closed_axioms manuscriptPrintedDefect_normal
#audit_closed_axioms manuscriptNormalClosureDefect_le_printedDefect
#audit_closed_axioms manuscriptPrintedDefect_eq_top_from_normalGeneration
#audit_closed_axioms manuscriptRadical_eq_top_from_criterion_with_K_eq_H
#audit_closed_axioms manuscriptActualRadical_eq_top_from_literalRadical
#audit_closed_axioms manuscriptNontrivial_and_simple_independently
#audit_axioms manuscriptEveryMapToMF_is_trivial
#audit_closed_axioms manuscriptIdentityMap_contradicts_MF

end RankTwelveEndpoint
end OneSidedMFRadical
end Manuscript
end GroupApproximation
