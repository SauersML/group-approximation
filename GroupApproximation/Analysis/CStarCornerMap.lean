import GroupApproximation.Analysis.CStarCorner
import GroupApproximation.Meta.AxiomGuard

/-!
# Functoriality of unital C-star corners

A unital star-algebra homomorphism which carries one corner projection to
another restricts to a unital star-algebra homomorphism of the corresponding
corners.
-/

namespace GroupApproximation
namespace CStarCorner

open scoped CStarAlgebra

noncomputable section

universe u v

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
variable {e : A} {f : B}
variable {he_star : star e = e} {hf_star : star f = f}
variable {he_mul : e * e = e} {hf_mul : f * f = f}

/-- Restriction of a unital star-algebra homomorphism to two corresponding
corners. -/
def map (Phi : A →⋆ₐ[ℂ] B) (hPhi : Phi e = f) :
    CStarCorner e he_star he_mul →⋆ₐ[ℂ]
      CStarCorner f hf_star hf_mul where
  toFun x := ⟨Phi (x : A), by
    constructor
    · rw [← hPhi, ← map_mul, x.property.1]
    · rw [← hPhi, ← map_mul, x.property.2]⟩
  map_one' := by
    apply Subtype.ext
    exact hPhi
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul Phi (x : A) (y : A)
  map_zero' := by
    apply Subtype.ext
    exact map_zero Phi
  map_add' x y := by
    apply Subtype.ext
    exact map_add Phi (x : A) (y : A)
  commutes' r := by
    apply Subtype.ext
    change Phi (algebraMap ℂ (CStarCorner e he_star he_mul) r : A) =
      (algebraMap ℂ (CStarCorner f hf_star hf_mul) r : B)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change Phi (r • e) = r • f
    rw [map_smul, hPhi]
  map_star' x := by
    apply Subtype.ext
    exact map_star Phi (x : A)

@[simp] theorem map_apply_coe
    (Phi : A →⋆ₐ[ℂ] B) (hPhi : Phi e = f)
    (x : CStarCorner e he_star he_mul) :
    ((map Phi hPhi x : CStarCorner f hf_star hf_mul) : B) = Phi (x : A) :=
  rfl

/-- Corner restriction is functorial for projection-preserving unital
star-algebra homomorphisms. -/
theorem map_exists
    (Phi : A →⋆ₐ[ℂ] B) (hPhi : Phi e = f) :
    ∃ Psi : CStarCorner e he_star he_mul →⋆ₐ[ℂ]
        CStarCorner f hf_star hf_mul,
      ∀ x, (Psi x : B) = Phi (x : A) :=
  ⟨map Phi hPhi, fun _ ↦ rfl⟩

/-- Closed universal form of corner functoriality. -/
def CornerMapFunctorial : Prop :=
  ∀ {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
    {e : A} {f : B}
    {he_star : star e = e} {hf_star : star f = f}
    {he_mul : e * e = e} {hf_mul : f * f = f}
    (Phi : A →⋆ₐ[ℂ] B), Phi e = f →
      ∃ Psi : CStarCorner e he_star he_mul →⋆ₐ[ℂ]
          CStarCorner f hf_star hf_mul,
        ∀ x, (Psi x : B) = Phi (x : A)

/-- Projection-preserving unital maps restrict to maps of corners. -/
theorem cornerMapFunctorial : CornerMapFunctorial := by
  intro A B _ _ e f he_star hf_star he_mul hf_mul Phi hPhi
  exact map_exists Phi hPhi

end

end CStarCorner
end GroupApproximation

#audit_closed_axioms GroupApproximation.CStarCorner.cornerMapFunctorial
