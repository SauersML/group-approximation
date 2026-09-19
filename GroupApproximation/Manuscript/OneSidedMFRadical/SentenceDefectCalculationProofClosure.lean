import GroupApproximation.Leavitt.ElementaryNormalGeneration
import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveConfiguration
import GroupApproximation.Meta.AxiomGuard

/-!
# Sentence-level closure of the explicit defect calculation

The proof of Proposition `prop:defect` in `non_mf_groups_exist.tex` gives a
short sequence of distinct algebraic reasons.  This file exposes every link of
that sequence as a separate declaration: the moved-mark multiplication, the
commuting second factor, the concrete Steinberg commutator, nontriviality from
the nonzero coefficient, the displayed unit sandwich, and normal generation
from that particular sandwich.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RankTwelveEndpoint

open scoped commutatorElement

/-- Direct multiplication of the printed matrices gives
`tau c tau⁻¹ = e₀₁(q)c`. -/
theorem manuscriptMovedMark_directMultiplication :
    tau * c * tau⁻¹ =
      elementaryRoot (0 : Fin 12) 1 (by decide) q * c :=
  tau_conj_c

/-- The second factor in the moved mark commutes with
`ell = e₁₂(1)`. -/
theorem manuscriptMovedMark_secondFactor_commutes :
    Commute c ell :=
  c_commutes_corner ell ell_mem_corner

/-- The concrete Steinberg relation used after the commuting factor has been
removed. -/
theorem manuscriptMovedMark_Steinberg_commutator :
    ⁅elementaryRoot (0 : Fin 12) 1 (by decide) q, ell⁆ = defect := by
  simpa only [ell, defect, mul_one] using
    (elementaryRoot_commutator (R := R) (0 : Fin 12) 1 2
      (by decide) (by decide) (by decide) q 1)

/-- Combining the preceding three calculations gives the displayed defect
identity, with the commuting-factor removal visible in the proof term. -/
theorem manuscriptMovedMark_defectCalculation :
    ⁅tau * c * tau⁻¹, ell⁆ = defect := by
  rw [manuscriptMovedMark_directMultiplication]
  rw [HilbertHotel.commutator_mul_left_of_commute _ _ _
    manuscriptMovedMark_secondFactor_commutes]
  exact manuscriptMovedMark_Steinberg_commutator

/-- The coefficient `q` is nonzero by its displayed Leavitt sandwich. -/
theorem manuscriptQ_ne_zero_from_unitSandwich : q ≠ 0 := by
  intro hq
  have hsandwich :
      leavittFamily.t1 * q * leavittFamily.s1 = 1 :=
    leavittFamily.t1_mul_p1_mul_s1
  rw [hq, mul_zero, zero_mul] at hsandwich
  exact zero_ne_one hsandwich

/-- Hence the elementary root `d=e₀₂(q)` is nonidentity. -/
theorem manuscriptDefect_ne_one_from_q_ne_zero : defect ≠ 1 := by
  intro hdefect
  apply manuscriptQ_ne_zero_from_unitSandwich
  exact (elGen_eq_one_iff (0 : Fin 12) 2 (by decide) q).mp hdefect

/-- The exact sandwich printed before the normal-generation invocation. -/
theorem manuscriptQ_unitSandwich :
    leavittFamily.t1 * q * leavittFamily.s1 = 1 :=
  leavittFamily.t1_mul_p1_mul_s1

/-- Applying elementary-root normal generation to the displayed sandwich
gives the whole rank-twelve elementary group. -/
theorem manuscriptDefectNormallyGenerates_from_printedSandwich :
    Subgroup.normalClosure ({defect} : Set H) = ⊤ := by
  simpa only [defect] using
    (normalClosure_elementaryRoot_eq_top_of_unit_sandwich
      (R := R) (ι := Fin 12) (by simp) (i := (0 : Fin 12))
      (j := (2 : Fin 12)) (by decide)
      ⟨leavittFamily.t1, leavittFamily.s1, manuscriptQ_unitSandwich⟩)

#audit_closed_axioms manuscriptMovedMark_directMultiplication
#audit_closed_axioms manuscriptMovedMark_secondFactor_commutes
#audit_closed_axioms manuscriptMovedMark_Steinberg_commutator
#audit_closed_axioms manuscriptMovedMark_defectCalculation
#audit_closed_axioms manuscriptQ_ne_zero_from_unitSandwich
#audit_closed_axioms manuscriptDefect_ne_one_from_q_ne_zero
#audit_closed_axioms manuscriptQ_unitSandwich
#audit_closed_axioms manuscriptDefectNormallyGenerates_from_printedSandwich

end RankTwelveEndpoint
end OneSidedMFRadical
end Manuscript
end GroupApproximation
