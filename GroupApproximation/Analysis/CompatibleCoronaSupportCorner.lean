import GroupApproximation.Analysis.NonUnitalMFSupportCornerEmbedding
import GroupApproximation.Meta.AxiomGuard

/-!
# A common support corner for compatible corona embeddings

Compatible faithful nonunital representations of two unital C-star algebras
have the same support projection: both support projections are the image of
the unit of the common unital subalgebra.  Consequently one projection lift
and one relabelled sequence of finite matrix corners unitalize both
representations simultaneously.

This is the support-corner reconciliation needed before applying the unital
universal-amalgam API in Shulman's compatible-corona argument.  It is
independent of the symmetric-double MF theorem and does not assume any
amalgam permanence statement.
-/

namespace GroupApproximation
namespace CompatibleCoronaSupportCorner

open NonUnitalMFSupportCorner
open NonUnitalMFSupportCornerEmbedding

noncomputable section

universe u v w

variable {C : Type u} {A : Type v} {B : Type w}
  [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]
  [Nontrivial A]

omit [Nontrivial A] in
/-- Compatible nonunital representations along unital factor inclusions have
the same support projection. -/
theorem supportProjection_eq_of_comp_eq
    (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
    (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    (left : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (right : B →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (hcompatible : left.comp iA.toNonUnitalStarAlgHom =
      right.comp iB.toNonUnitalStarAlgHom) :
    supportProjection Y left = supportProjection Y right := by
  change left 1 = right 1
  have hunit := DFunLike.congr_fun hcompatible (1 : C)
  change left (iA 1) = right (iB 1) at hunit
  simpa only [map_one] using hunit

/-- A compatible faithful pair of possibly nonunital corona embeddings can be
unitalized in one common relabelled support-corner corona. -/
theorem exists_compatible_injective_unital_supportCornerEmbeddings
    (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
    (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    (left : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (right : B →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hcompatible : left.comp iA.toNonUnitalStarAlgHom =
      right.comp iB.toNonUnitalStarAlgHom) :
    ∃ Z : ℕ → FiniteModel, ∃ hZne : ∀ n, Nonempty (Z n),
      letI : ∀ n, Nonempty (Z n) := hZne
      ∃ left' : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Z n),
        ∃ right' : B →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Z n),
          Function.Injective left' ∧ Function.Injective right' ∧
            left'.comp iA = right'.comp iB := by
  obtain ⟨P, hP, hPmkLeft, _hPinfinite⟩ :=
    exists_projection_lift_with_infinite_support Y left hleft
  have hsupport : supportProjection Y left = supportProjection Y right :=
    supportProjection_eq_of_comp_eq Y iA iB left right hcompatible
  have hPmkRight :
      normMatrixCStarCoronaMk (fun n ↦ Y n) P = supportProjection Y right :=
    hPmkLeft.trans hsupport
  have hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0 := by
    rw [hPmkLeft]
    exact supportProjection_ne_zero Y left hleft
  let Z : ℕ → FiniteModel := fun k ↦ relabelledCornerModel Y P hP hne k
  let hZne : ∀ n, Nonempty (Z n) := fun k ↦
    relabelledCornerModel_nonempty Y P hP hne k
  let left' : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Z n) :=
    supportCornerEmbedding Y left P hP hPmkLeft hne
  let right' : B →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Z n) :=
    supportCornerEmbedding Y right P hP hPmkRight hne
  refine ⟨Z, hZne, left', right', ?_, ?_, ?_⟩
  · exact supportCornerEmbedding_injective Y left hleft P hP hPmkLeft hne
  · exact supportCornerEmbedding_injective Y right hright P hP hPmkRight hne
  · apply StarAlgHom.ext
    intro c
    change sourceCornerClass Y left P hP hne (iA c) =
      sourceCornerClass Y right P hP hne (iB c)
    rw [sourceCornerClass, sourceCornerClass]
    apply cornerClass_eq_of_mk_eq
    rw [sourceSandwich_spec Y left P hPmkLeft,
      sourceSandwich_spec Y right P hPmkRight]
    exact DFunLike.congr_fun hcompatible c

/-- Closed universal form of the common support-corner theorem. -/
def CompatibleEmbeddingsHaveCommonUnitalSupportCorner : Prop :=
  ∀ {C : Type u} {A : Type v} {B : Type w}
    [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]
    [Nontrivial A]
    (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
    (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    (left : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (right : B →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n)),
    Function.Injective left → Function.Injective right →
      left.comp iA.toNonUnitalStarAlgHom =
        right.comp iB.toNonUnitalStarAlgHom →
      ∃ Z : ℕ → FiniteModel, ∃ hZne : ∀ n, Nonempty (Z n),
        letI : ∀ n, Nonempty (Z n) := hZne
        ∃ left' : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Z n),
          ∃ right' : B →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Z n),
            Function.Injective left' ∧ Function.Injective right' ∧
              left'.comp iA = right'.comp iB

/-- Compatible faithful nonunital corona embeddings admit a common faithful
unital support-corner realization. -/
theorem compatibleEmbeddingsHaveCommonUnitalSupportCorner :
    CompatibleEmbeddingsHaveCommonUnitalSupportCorner := by
  intro C A B _ _ _ _ Y _ iA iB left right hleft hright hcompatible
  exact exists_compatible_injective_unital_supportCornerEmbeddings
    Y iA iB left right hleft hright hcompatible

end

end CompatibleCoronaSupportCorner
end GroupApproximation

#audit_closed_axioms GroupApproximation.CompatibleCoronaSupportCorner.compatibleEmbeddingsHaveCommonUnitalSupportCorner
