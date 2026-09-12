import GroupApproximation.Algebra.GroupRingStar
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Unitary covariance on a commutative C-star subalgebra

This module isolates the formal covariance step needed for the integral
root-plane argument.  If unitary conjugation and its inverse preserve a closed
commutative star subalgebra, conjugation restricts to a star-algebra
automorphism of that subalgebra.  Gelfand duality then gives the contravariant
homeomorphism of its character space, with the expected evaluation formula.

The final coordinate lemma says exactly how any family of represented plane
coordinates transforms.  No state, measure, Haar integral, disintegration, or
measure-existence statement occurs here.
-/

namespace GroupApproximation

namespace CommutativeCStarCovariance

open WeakDual

universe u v

variable {A : Type u} [CStarAlgebra A]

/-- Restriction of ambient unitary conjugation to an invariant star
subalgebra. -/
noncomputable def restrictConjStarAlgHom (S : StarSubalgebra ℂ A) (u : unitary A)
    (hforward : ∀ x : S, Unitary.conjStarAlgAut ℂ A u x.1 ∈ S) :
    S →⋆ₐ[ℂ] S :=
  ((Unitary.conjStarAlgAut ℂ A u).toStarAlgHom.comp S.subtype).codRestrict
    S hforward

@[simp] theorem restrictConjStarAlgHom_coe
    (S : StarSubalgebra ℂ A) (u : unitary A)
    (hforward : ∀ x : S, Unitary.conjStarAlgAut ℂ A u x.1 ∈ S)
    (x : S) :
    ((restrictConjStarAlgHom S u hforward x : S) : A) =
      Unitary.conjStarAlgAut ℂ A u x.1 :=
  rfl

/-- If conjugation and inverse conjugation preserve `S`, ambient conjugation
restricts to a star-algebra automorphism of `S`. -/
noncomputable def restrictConjStarAlgEquiv
    (S : StarSubalgebra ℂ A) (u : unitary A)
    (hforward : ∀ x : S, Unitary.conjStarAlgAut ℂ A u x.1 ∈ S)
    (hbackward : ∀ x : S,
      (Unitary.conjStarAlgAut ℂ A u).symm x.1 ∈ S) :
    S ≃⋆ₐ[ℂ] S := by
  let f : S →⋆ₐ[ℂ] S := restrictConjStarAlgHom S u hforward
  let g : S →⋆ₐ[ℂ] S :=
    ((Unitary.conjStarAlgAut ℂ A u).symm.toStarAlgHom.comp S.subtype).codRestrict
      S hbackward
  have hgf : g.comp f = StarAlgHom.id ℂ S := by
    apply StarAlgHom.ext
    intro x
    apply Subtype.ext
    exact (Unitary.conjStarAlgAut ℂ A u).symm_apply_apply x.1
  have hfg : f.comp g = StarAlgHom.id ℂ S := by
    apply StarAlgHom.ext
    intro x
    apply Subtype.ext
    exact (Unitary.conjStarAlgAut ℂ A u).apply_symm_apply x.1
  exact StarAlgEquiv.ofStarAlgHom f g hgf hfg

@[simp] theorem restrictConjStarAlgEquiv_coe
    (S : StarSubalgebra ℂ A) (u : unitary A)
    (hforward : ∀ x : S, Unitary.conjStarAlgAut ℂ A u x.1 ∈ S)
    (hbackward : ∀ x : S,
      (Unitary.conjStarAlgAut ℂ A u).symm x.1 ∈ S)
    (x : S) :
    ((restrictConjStarAlgEquiv S u hforward hbackward x : S) : A) =
      Unitary.conjStarAlgAut ℂ A u x.1 :=
  rfl

/-- Coercion formula for the inverse restricted conjugation equivalence. -/
@[simp] theorem restrictConjStarAlgEquiv_symm_coe
    (S : StarSubalgebra ℂ A) (u : unitary A)
    (hforward : ∀ x : S, Unitary.conjStarAlgAut ℂ A u x.1 ∈ S)
    (hbackward : ∀ x : S,
      (Unitary.conjStarAlgAut ℂ A u).symm x.1 ∈ S)
    (x : S) :
    (((restrictConjStarAlgEquiv S u hforward hbackward).symm x : S) : A) =
      (Unitary.conjStarAlgAut ℂ A u).symm x.1 :=
  rfl

section CharacterAction

variable (S : StarSubalgebra ℂ A) [CompleteSpace S]

/-- The contravariant action of the restricted conjugation automorphism on
Gelfand characters. -/
noncomputable def characterAction (u : unitary A)
    (hforward : ∀ x : S, Unitary.conjStarAlgAut ℂ A u x.1 ∈ S)
    (hbackward : ∀ x : S,
      (Unitary.conjStarAlgAut ℂ A u).symm x.1 ∈ S) :
    C(characterSpace ℂ S, characterSpace ℂ S) :=
  CharacterSpace.compContinuousMap
    (restrictConjStarAlgEquiv S u hforward hbackward).toStarAlgHom

/-- Pullback by the restricted automorphism is a homeomorphism of the
character space. -/
noncomputable def characterHomeomorph (u : unitary A)
    (hforward : ∀ x : S, Unitary.conjStarAlgAut ℂ A u x.1 ∈ S)
    (hbackward : ∀ x : S,
      (Unitary.conjStarAlgAut ℂ A u).symm x.1 ∈ S) :
    characterSpace ℂ S ≃ₜ characterSpace ℂ S where
  toFun := characterAction S u hforward hbackward
  invFun := CharacterSpace.compContinuousMap
    (restrictConjStarAlgEquiv S u hforward hbackward).symm.toStarAlgHom
  left_inv χ := by
    apply CharacterSpace.ext
    intro x
    change χ (restrictConjStarAlgEquiv S u hforward hbackward
      ((restrictConjStarAlgEquiv S u hforward hbackward).symm x)) = χ x
    exact congrArg (fun y : S ↦ χ y)
      ((restrictConjStarAlgEquiv S u hforward hbackward).apply_symm_apply x)
  right_inv χ := by
    apply CharacterSpace.ext
    intro x
    change χ ((restrictConjStarAlgEquiv S u hforward hbackward).symm
      (restrictConjStarAlgEquiv S u hforward hbackward x)) = χ x
    exact congrArg (fun y : S ↦ χ y)
      ((restrictConjStarAlgEquiv S u hforward hbackward).symm_apply_apply x)
  continuous_toFun := (characterAction S u hforward hbackward).continuous
  continuous_invFun := (CharacterSpace.compContinuousMap
    (restrictConjStarAlgEquiv S u hforward hbackward).symm.toStarAlgHom).continuous

/-- Evaluation after the character action is evaluation before the action at
the conjugated algebra element. -/
@[simp] theorem characterAction_apply_apply
    (u : unitary A)
    (hforward : ∀ x : S, Unitary.conjStarAlgAut ℂ A u x.1 ∈ S)
    (hbackward : ∀ x : S,
      (Unitary.conjStarAlgAut ℂ A u).symm x.1 ∈ S)
    (χ : characterSpace ℂ S) (x : S) :
    characterAction S u hforward hbackward χ x =
      χ (restrictConjStarAlgEquiv S u hforward hbackward x) :=
  rfl

/-- Coordinate form of covariance.  If conjugation sends coordinate `c i` to
`c (sigma i)`, the induced character action pulls the evaluation at `i` back
to evaluation at `sigma i`. -/
theorem characterAction_coordinate
    {I : Type v} (c : I → S) (sigma : I → I)
    (u : unitary A)
    (hforward : ∀ x : S, Unitary.conjStarAlgAut ℂ A u x.1 ∈ S)
    (hbackward : ∀ x : S,
      (Unitary.conjStarAlgAut ℂ A u).symm x.1 ∈ S)
    (hcoordinate : ∀ i,
      restrictConjStarAlgEquiv S u hforward hbackward (c i) = c (sigma i))
    (χ : characterSpace ℂ S) (i : I) :
    characterAction S u hforward hbackward χ (c i) = χ (c (sigma i)) := by
  rw [characterAction_apply_apply, hcoordinate]

end CharacterAction

/-! ### Covariance of a represented subgroup -/

/-- Conjugation of a represented group element is representation of the group
conjugate.  This is the ambient identity used to verify the invariant-subalgebra
hypotheses above for a root plane normalized by an elementary shear. -/
theorem conjStarAlgAut_representation_apply
    {G : Type v} [Group G] (rho : G →* unitary A) (g h : G) :
    Unitary.conjStarAlgAut ℂ A (rho g) (rho h : A) =
      (rho (g * h * g⁻¹) : A) := by
  rw [Unitary.conjStarAlgAut_apply,
    ← GroupRingStar.coe_unitary_inv (rho g), ← map_inv]
  have hu : rho g * rho h * rho (g⁻¹) = rho (g * h * g⁻¹) := by
    rw [← map_mul, ← map_mul]
  exact congrArg (fun u : unitary A ↦ (u : A)) hu

end CommutativeCStarCovariance

end GroupApproximation
