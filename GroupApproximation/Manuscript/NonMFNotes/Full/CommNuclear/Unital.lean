import GroupApproximation.Analysis.CStarContinuousMapNuclear
import GroupApproximation.Analysis.CStarNuclearRetract
import GroupApproximation.Analysis.KKTheoryKasparov
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.Normed.Algebra.Basic

/-!
# Commutative unital C⋆-algebras are nuclear (Brown--Ozawa, Prop. 2.4.2)

Used in `non_mf_group_notes.tex` along the Tikuisis--White--Winter /
Schafhauser route to `thm:fixed-radical-membership` (the
Rosenberg--Schochet injectivity step needs the commutative model of a
bootstrap algebra to be nuclear).  Source: Brown--Ozawa, *C⋆-algebras and
finite-dimensional approximations*, Proposition 2.4.2; Takesaki IV.3.

## Proof

By Gelfand duality (`gelfandStarTransform`) a unital commutative C⋆-algebra
`A` is ⋆-isomorphic to `C(X, ℂ)` with `X` the (compact Hausdorff) character
space.  For `C(X, ℂ)` the completely positive approximation property is
already proved on `main`, by the explicit partition-of-unity argument:

* `CStarContinuousMapFiniteInterpolation.exists_variation_partition` --- a
  finite cover by sets on which the given finite family oscillates by less
  than `ε`, with a subordinate continuous partition of unity `w i` and sample
  points `x i`;
* `finiteEvaluationStarAlgHom` --- the ⋆-homomorphism `f ↦ (f (x i))ᵢ` into
  the finite-dimensional C⋆-algebra `Fin k → ℂ` (completely positive and
  contractive as a ⋆-homomorphism);
* `finiteInterpolation`, `isCompletelyPositive_finiteInterpolation`,
  `norm_finiteInterpolation_le` --- the positive map
  `(λᵢ) ↦ ∑ λᵢ • w i` out of `Fin k → ℂ`, proved completely positive (as a
  sum of the maps `λ ↦ λᵢ • w i`, each a compression of a coordinate
  ⋆-homomorphism by `√(w i)`) and contractive because `∑ w i = 1`;
* `isNuclearCStarAlgebra_continuousMap` --- the assembled CPAP.

Nuclearity is then transported along the Gelfand isomorphism with the
completely positive contractive retract lemma
`CStarExactness.IsNuclearCStarAlgebra.of_cpContractiveRetract`.  The zero
algebra (empty character space) is treated separately.

## Main results

* `isNuclearCStarAlgebra_of_commCStarAlgebra` --- for `[CommCStarAlgebra A]`;
* `isNuclearCStarAlgebra_of_commutative` --- for a `CStarAlgebra` whose
  multiplication commutes;
* `nuclear_of_commutative` --- the `KK.SepCStarAlgebra` form consumed by the
  Schafhauser lane (`TWWSch3d3-3D`).
-/

namespace GroupApproximation.Full.CommNuclear

universe u

noncomputable section

/-- The zero C⋆-algebra is nuclear: it is a completely positive contractive
retract of `ℂ` through the zero maps. -/
theorem isNuclearCStarAlgebra_of_subsingleton (A : Type u) [NonUnitalCStarAlgebra A]
    [Subsingleton A] : CStarExactness.IsNuclearCStarAlgebra A := by
  refine CStarExactness.IsNuclearCStarAlgebra.of_cpContractiveRetract
    (0 : A →⋆ₙₐ[ℂ] ℂ) (0 : ℂ →ₗ[ℂ] A) ?_ ?_ ?_ CStarExactness.isNuclearCStarAlgebra_complex
  · intro _ _ _
    refine ⟨0, ?_⟩
    exact CStarMatrix.ext fun _ _ => Subsingleton.elim _ _
  · intro b
    rw [LinearMap.zero_apply, norm_zero]
    exact norm_nonneg b
  · intro _
    exact Subsingleton.elim _ _

/-- **Brown--Ozawa, Prop. 2.4.2 (unital case).**  Every unital commutative
C⋆-algebra is nuclear, i.e. has the completely positive approximation
property.  Gelfand duality identifies it with `C(X, ℂ)`, whose CPAP is the
partition-of-unity theorem `isNuclearCStarAlgebra_continuousMap`. -/
theorem isNuclearCStarAlgebra_of_commCStarAlgebra (A : Type u) [CommCStarAlgebra A] :
    CStarExactness.IsNuclearCStarAlgebra A := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact isNuclearCStarAlgebra_of_subsingleton A
  · exact CStarExactness.IsNuclearCStarAlgebra.of_cpContractiveRetract
      (gelfandStarTransform A).toNonUnitalStarAlgHom
      ((gelfandStarTransform A).symm.toNonUnitalStarAlgHom :
        C(WeakDual.characterSpace ℂ A, ℂ) →ₗ[ℂ] A)
      (CStarExactness.isCompletelyPositive_of_starAlgHom
        (gelfandStarTransform A).symm.toNonUnitalStarAlgHom)
      (fun b => NonUnitalStarAlgHom.norm_apply_le
        (gelfandStarTransform A).symm.toNonUnitalStarAlgHom b)
      (fun a => (gelfandStarTransform A).symm_apply_apply a)
      CStarContinuousMapFiniteInterpolation.isNuclearCStarAlgebra_continuousMap

/-- **Brown--Ozawa, Prop. 2.4.2**, hypothesis form: a (unital) C⋆-algebra
whose multiplication commutes is nuclear.  The commutative instance is
assembled locally from `hcomm`; it agrees with the ambient structure by
structure eta. -/
theorem isNuclearCStarAlgebra_of_commutative {A : Type u} [CStarAlgebra A]
    (hcomm : ∀ a b : A, a * b = b * a) : CStarExactness.IsNuclearCStarAlgebra A := by
  letI : CommCStarAlgebra A :=
    { (inferInstance : CStarAlgebra A) with mul_comm := hcomm }
  exact isNuclearCStarAlgebra_of_commCStarAlgebra A

/-- **Commutative separable C⋆-algebras are nuclear** (Brown--Ozawa,
Prop. 2.4.2), in the bundled `KK.SepCStarAlgebra` form used by the
Rosenberg--Schochet step of `thm:fixed-radical-membership`
(`non_mf_group_notes.tex`).  Separability is not needed. -/
theorem nuclear_of_commutative {C : KK.SepCStarAlgebra.{u}} (hC : C.IsCommutative) :
    CStarExactness.IsNuclearCStarAlgebra C :=
  isNuclearCStarAlgebra_of_commutative hC

end

end GroupApproximation.Full.CommNuclear
