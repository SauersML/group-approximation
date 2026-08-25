import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoints
import GroupApproximation.Meta.AxiomGuard

/-!
# The printed upper-left-corner centralizer calculation

This module formalizes the two sentences at the start of the proof of
`prop:defect` without collapsing their intermediate calculation into the
already proved endpoint `c_commutes_corner`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RankTwelveEndpoint

open scoped commutatorElement

/-- For a literal upper-left `3 × 3` root, the two index inequalities used by
the printed Steinberg-commutation step hold, and the displayed commutator with
`c = e₃₄(1)` is the identity. -/
theorem manuscriptCornerGenerator_commutator_eq_one
    (i j : Fin 3) (hij : i ≠ j) (a : R) :
    cornerIndex j ≠ (3 : Fin 12) ∧
      cornerIndex i ≠ (4 : Fin 12) ∧
      ⁅elementaryRoot (cornerIndex i) (cornerIndex j)
          (cornerIndex_injective.ne hij) a, c⁆ = 1 := by
  have hj3 : cornerIndex j ≠ (3 : Fin 12) := by
    intro h
    have hval := congrArg Fin.val h
    simp [cornerIndex] at hval
    omega
  have hi4 : cornerIndex i ≠ (4 : Fin 12) := by
    intro h
    have hval := congrArg Fin.val h
    simp [cornerIndex] at hval
    omega
  refine ⟨hj3, hi4, ?_⟩
  apply commutatorElement_eq_one_iff_commute.mpr
  unfold c
  exact elementaryRoot_commute_of_ne
    (cornerIndex i) (cornerIndex j) (3 : Fin 12) 4
    (cornerIndex_injective.ne hij) (by decide) hj3 hi4.symm a 1

/-- The roots quantified in the preceding theorem are exactly the generating
set used to define the manuscript's upper-left subgroup `L`. -/
theorem manuscriptCornerRoots_generate :
    corner = Subgroup.closure cornerRootSet :=
  rfl

/-- Since `c` commutes with every printed corner generator, it belongs to the
centralizer of the entire printed subgroup `L`. -/
theorem manuscriptC_mem_cornerCentralizer :
    c ∈ Subgroup.centralizer (corner : Set H) := by
  rw [Subgroup.mem_centralizer_iff]
  intro gamma hgamma
  exact (c_commutes_corner gamma hgamma).symm

#audit_closed_axioms manuscriptCornerRoots_generate
#audit_closed_axioms manuscriptC_mem_cornerCentralizer
#audit_axioms manuscriptCornerGenerator_commutator_eq_one

end RankTwelveEndpoint
end OneSidedMFRadical
end Manuscript
end GroupApproximation
