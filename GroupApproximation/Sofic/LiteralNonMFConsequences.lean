import GroupApproximation.Analysis.MFAlgebra
import GroupApproximation.Sofic.LiteralNonMFEndpoint

/-!
# Exact faithful-target consequence for the literal group

The target algebra may sit as a nonunital C-star subalgebra of a matrix
corona.  Its unitary group therefore enters the ambient unitary group by the
corner-complement correction `u ↦ e(u) + (1 - e(1))`, not by the raw
possibly nonunital homomorphism.
-/

namespace GroupApproximation
namespace LiteralNonMFConsequences

open LiteralNonMFPresentation

noncomputable section

universe u

/-- The literal group admits no faithful unitary representation in a unital
C-star algebra that embeds, possibly nonunitally, in a natural-dimension norm
matrix corona. -/
theorem literal_no_faithful_corona_subalgebra_target :
    ∀ (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
      letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
        fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
      ∀ (A : Type u) [CStarAlgebra A]
      (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona
        (fun n ↦ naturalFiniteModel (d n))),
      Function.Injective e →
        ∀ rho : MarkedGroup →* unitary A, ¬ Function.Injective rho := by
  intro d hd A _ e he rho hrho
  letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
    fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
  let corrected : unitary A →*
      unitary (NormMatrixCStarCorona
        (fun n ↦ naturalFiniteModel (d n))) :=
    nonUnitalStarAlgHomUnitaryMap e
  let Theta : MarkedGroup →*
      unitary (NormMatrixCStarCorona
        (fun n ↦ naturalFiniteModel (d n))) := corrected.comp rho
  have hTheta : Theta mark = 1 :=
    LiteralNonMFEndpoint.literal_mark_eq_one_in_CStarCorona d hd Theta
  have hThetaInjective : Function.Injective Theta :=
    (nonUnitalStarAlgHomUnitaryMap_injective he).comp hrho
  exact LiteralNonMFLinearWitness.literal_mark_ne_one
    (hThetaInjective (by simpa [Theta] using hTheta))

end

end LiteralNonMFConsequences
end GroupApproximation
