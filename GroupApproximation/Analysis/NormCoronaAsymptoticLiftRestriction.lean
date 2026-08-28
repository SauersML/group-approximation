import GroupApproximation.Analysis.NormCoronaAsymptoticLiftCore

/-!
# Restricting a norm-corona asymptotic lift along a homomorphism
-/

namespace GroupApproximation
namespace NormCoronaAsymptoticLift

open Filter
open scoped Matrix.Norms.L2Operator

noncomputable section

-- The two algebras are at independent universes: the universal amalgam of
-- algebras in `Type u` lives in `Type (u + 1)`, so a consumer restricting a
-- corona homomorphism along a factor map has `A` and `U` one level apart.
variable {A U : Type*} [CStarAlgebra A] [CStarAlgebra U]

/-- If a corona homomorphism restricts exactly to another corona
homomorphism, their chosen coordinate lifts agree asymptotically in norm. -/
theorem tendsto_model_map_sub_of_comp_eq
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (i : A →⋆ₐ[ℂ] U)
    (Phi : U →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (f : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (h : Phi.comp i = f) (a : A) :
    Tendsto
      (fun n ↦ ‖(model Phi.toNonUnitalStarAlgHom).map n (i a) -
        (model f.toNonUnitalStarAlgHom).map n a‖)
      atTop (nhds 0) := by
  apply KirchbergRordam.tendsto_norm_sub_of_corona_eq
  rw [mk_lift, mk_lift]
  exact DFunLike.congr_fun h a

end

end NormCoronaAsymptoticLift
end GroupApproximation
