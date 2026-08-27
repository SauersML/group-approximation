import GroupApproximation.Analysis.KirchbergRordamCorona
import GroupApproximation.Sofic.Sofic

/-!
# Representatives and the discrete asymptotic-model interface

This file contains only the model structure and the choice of a bounded
representative of each corona element.  Algebraic-defect proofs and the model
constructor are in `NormCoronaAsymptoticLiftCore`.
-/

namespace GroupApproximation
namespace NormCoronaAsymptoticLift

open Filter
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n).carrier]

/-- A discrete operator-norm asymptotic star homomorphism into a sequence of
full matrix algebras.  The maps are deliberately not assumed linear. -/
structure Model (A : Type u) [NonUnitalCStarAlgebra A] where
  map : ∀ n : ℕ, A → Matrix (X n).carrier (X n).carrier ℂ
  tendsto_mul : ∀ a b : A,
    Tendsto (fun n ↦ ‖map n (a * b) - map n a * map n b‖) atTop (nhds 0)
  tendsto_add : ∀ a b : A,
    Tendsto (fun n ↦ ‖map n (a + b) - (map n a + map n b)‖) atTop (nhds 0)
  tendsto_smul : ∀ (c : ℂ) (a : A),
    Tendsto (fun n ↦ ‖map n (c • a) - c • map n a‖) atTop (nhds 0)
  tendsto_star : ∀ a : A,
    Tendsto (fun n ↦ ‖map n (star a) - star (map n a)‖) atTop (nhds 0)
  bounded : ∀ a : A, ∃ C : ℝ, ∀ n : ℕ, ‖map n a‖ ≤ C

/-- A fixed bounded representative of the image of one source element. -/
def lift {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier)) (a : A) :
    BoundedMatrixSequence (fun n ↦ (X n).carrier) :=
  Function.surjInv
    (normMatrixCStarCoronaMk_surjective (fun n ↦ (X n).carrier)) (f a)

@[simp] theorem mk_lift {A : Type u} [NonUnitalCStarAlgebra A]
    (f : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ (X n).carrier)) (a : A) :
    normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (lift f a) = f a :=
  Function.surjInv_eq
    (normMatrixCStarCoronaMk_surjective (fun n ↦ (X n).carrier)) (f a)

end


end NormCoronaAsymptoticLift
end GroupApproximation
