import GroupApproximation.Analysis.ShulmanHalmosDilationCommutator
import GroupApproximation.Meta.AxiomGuard

/-! Closed endpoint for the Halmos dilation calculation. -/

namespace GroupApproximation
namespace ShulmanHalmosDilation

open scoped CStarAlgebra

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

noncomputable local instance : PartialOrder A := CStarAlgebra.spectralOrder A
noncomputable local instance : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

noncomputable local instance [Nontrivial A] :
    ContinuousFunctionalCalculus ℂ (Mat₂ A) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

noncomputable local instance [Nontrivial A] :
    ContinuousFunctionalCalculus ℝ (Mat₂ A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

noncomputable local instance [Nontrivial A] :
    PartialOrder (Mat₂ A) := CStarAlgebra.spectralOrder (Mat₂ A)

noncomputable local instance [Nontrivial A] :
    StarOrderedRing (Mat₂ A) := CStarAlgebra.spectralOrderedRing (Mat₂ A)

noncomputable local instance [Nontrivial A] :
    NonnegSpectrumClass ℝ (Mat₂ A) :=
  CStarAlgebra.instNonnegSpectrumClass

/-- Closed endpoint: the Halmos matrix of every contraction is unitary, and
its repeated-block commutator is controlled by the four displayed coordinate
commutators. -/
def HalmosDilationAndBlockCommutatorControl : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] [Nontrivial A] (x a : A),
    ‖x‖ ≤ 1 →
    halmos x ∈ unitary (Mat₂ A) ∧
    ‖halmos x * diag₂ a a - diag₂ a a * halmos x‖ ≤
      ‖x * a - a * x‖ +
      ‖leftDefect x * a - a * leftDefect x‖ +
      ‖rightDefect x * a - a * rightDefect x‖ +
      ‖(-star x) * a - a * (-star x)‖

theorem halmosDilationAndBlockCommutatorControl :
    HalmosDilationAndBlockCommutatorControl := by
  intro A _ _ x a hx
  exact ⟨halmos_mem_unitary hx, norm_halmos_commutator_diag₂_le x a⟩
end

end ShulmanHalmosDilation
end GroupApproximation

#audit_closed_axioms GroupApproximation.ShulmanHalmosDilation.halmosDilationAndBlockCommutatorControl
