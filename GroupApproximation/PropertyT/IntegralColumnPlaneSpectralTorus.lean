import GroupApproximation.PropertyT.IntegralColumnPlaneSpectralShear
import GroupApproximation.PropertyT.KassabovRankZeroTorusGeometry
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Scalar torus coordinates of the integral column-plane spectrum

Evaluation at the two unit-coefficient column roots sends every Gelfand
character of the represented column-plane algebra to the two-dimensional
additive torus.  This file constructs that map and proves that the abstract
character actions induced by the two elementary unit shears become the four
standard torus shears.  These are exact covariance statements; no measure
estimate is assumed.
-/

namespace GroupApproximation
namespace IntegralColumnPlaneSpectralTorus

open WeakDual MeasureTheory Set
open IntegralColumnPlaneSpectralMeasure IntegralColumnPlaneSpectralShear
open IntegralCharacterMass
open RepresentedRootPlaneSpectralMeasure CommutativeCStarCovariance

noncomputable section

universe u v

/-! ### Transport through a measurable semiconjugacy -/

/-- Quadratic measurable quasi-invariance descends through any measurable
semiconjugacy.  Injectivity or surjectivity of the factor map is not needed;
bijectivity of the two actions gives the exact preimage identity used in the
proof. -/
theorem measurableQuasiInvariantAtScale_map_of_semiconj
    {Omega Xi : Type*} [MeasurableSpace Omega] [MeasurableSpace Xi]
    (mu : Measure Omega) [IsFiniteMeasure mu] (epsilon : ℝ)
    (f : Omega → Xi) (hf : Measurable f)
    (h : Omega ≃ᵐ Omega) (g : Xi ≃ᵐ Xi)
    (hsemiconj : ∀ x, f (h x) = g (f x))
    (hquasi :
      KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
        mu epsilon h) :
    KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
      (Measure.map f mu) epsilon g := by
  intro B hB hgB
  have hpreB : MeasurableSet (f ⁻¹' B) := hB.preimage hf
  have himagePreB : MeasurableSet (h '' (f ⁻¹' B)) :=
    h.measurableSet_image.mpr hpreB
  have hpreimage : h '' (f ⁻¹' B) = f ⁻¹' (g '' B) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨f a, ha, (hsemiconj a).symm⟩
    · rintro ⟨b, hb, hgb⟩
      refine ⟨h.symm x, ?_, h.apply_symm_apply x⟩
      have hab : f (h.symm x) = b := by
        apply g.injective
        calc
          g (f (h.symm x)) = f (h (h.symm x)) := (hsemiconj _).symm
          _ = f x := congrArg f (h.apply_symm_apply x)
          _ = g b := hgb.symm
      change f (h.symm x) ∈ B
      rw [hab]
      exact hb
  rw [map_measureReal_apply hf hgB, map_measureReal_apply hf hB,
    ← hpreimage]
  exact hquasi (f ⁻¹' B) hpreB himagePreB

variable {R : Type u} [Ring R]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable (rho : elementaryGroup (Fin 3) R →* (E ≃ₗᵢ[ℝ] E))

private abbrev P := representedColumnPlane rho
private abbrev X := characterSpace ℂ (P rho).algebra

noncomputable local instance representedColumnPlaneCharacterMeasurableSpace :
    MeasurableSpace (X rho) :=
  borel _

local instance representedColumnPlaneCharacterBorelSpace :
    BorelSpace (X rho) :=
  ⟨rfl⟩

/-- Evaluation of a Gelfand character at a represented root coordinate lies
on the complex unit circle. -/
noncomputable def coordinateCircle (q : Fin 2 × R) (chi : X rho) : Circle := by
  refine ⟨chi ((P rho).coordinate q), ?_⟩
  have hunit :
      star ((P rho).coordinate q) * (P rho).coordinate q = 1 := by
    apply Subtype.ext
    change star (((P rho).rho ((P rho).root q) :
        unitary (Complexification E →L[ℂ] Complexification E)) :
          Complexification E →L[ℂ] Complexification E) *
        ((P rho).rho ((P rho).root q) :
          unitary (Complexification E →L[ℂ] Complexification E)) = 1
    exact ((P rho).rho ((P rho).root q)).property.1
  have hmapped := congrArg (fun a : (P rho).algebra ↦ chi a) hunit
  rw [map_mul, map_star, map_one] at hmapped
  have hnorm := congrArg norm hmapped
  rw [norm_mul, norm_star, norm_one] at hnorm
  have hone : ‖chi ((P rho).coordinate q)‖ = 1 := by
    nlinarith [norm_nonneg (chi ((P rho).coordinate q))]
  exact mem_sphere_zero_iff_norm.mpr hone

@[simp] theorem coordinateCircle_coe (q : Fin 2 × R) (chi : X rho) :
    (coordinateCircle rho q chi : ℂ) = chi ((P rho).coordinate q) :=
  rfl

theorem continuous_coordinateCircle (q : Fin 2 × R) :
    Continuous (coordinateCircle rho q) := by
  have hcomplex : Continuous (fun chi : X rho ↦
      chi ((P rho).coordinate q)) :=
    ((gelfandStarTransform (P rho).algebra)
      ((P rho).coordinate q)).continuous
  have hcircle : Continuous (fun chi : X rho ↦
      (⟨chi ((P rho).coordinate q), (coordinateCircle rho q chi).property⟩ :
        Circle)) :=
    hcomplex.subtype_mk (fun chi ↦ (coordinateCircle rho q chi).property)
  exact hcircle

/-- The additive-circle angle corresponding to one scalar root evaluation. -/
noncomputable def coordinateAngle (q : Fin 2 × R) (chi : X rho) :
    AddCircle (1 : ℝ) :=
  (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).symm
    (coordinateCircle rho q chi)

theorem continuous_coordinateAngle (q : Fin 2 × R) :
    Continuous (coordinateAngle rho q) :=
  (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).symm.continuous.comp
    (continuous_coordinateCircle rho q)

@[simp] theorem coordinateAngle_toCircle (q : Fin 2 × R) (chi : X rho) :
    (coordinateAngle rho q chi).toCircle = coordinateCircle rho q chi := by
  rw [← AddCircle.homeomorphCircle_apply]
  exact (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).apply_symm_apply _

/-- Negating a root coefficient inverts its circle-valued character
coordinate. -/
theorem coordinateCircle_neg (b : Fin 2) (a : R) (chi : X rho) :
    coordinateCircle rho (b, -a) chi =
      (coordinateCircle rho (b, a) chi)⁻¹ := by
  apply Circle.ext
  change chi ((P rho).coordinate (b, -a)) =
    (chi ((P rho).coordinate (b, a)))⁻¹
  apply eq_inv_of_mul_eq_one_right
  have hcoord :
      (P rho).coordinate (b, a) * (P rho).coordinate (b, -a) = 1 := by
    apply Subtype.ext
    change ((((P rho).rho (columnRoot (b, a)) :
        unitary (Complexification E →L[ℂ] Complexification E)) :
          Complexification E →L[ℂ] Complexification E) *
        (((P rho).rho (columnRoot (b, -a)) :
          unitary (Complexification E →L[ℂ] Complexification E)) :
            Complexification E →L[ℂ] Complexification E)) = 1
    have hroot : columnRoot (b, -a) = (columnRoot (b, a))⁻¹ := by
      simp [columnRoot]
    rw [hroot, map_inv]
    exact ((P rho).rho (columnRoot (b, a))).property.2
  rw [← map_mul, hcoord, map_one]

/-- Negating a root coefficient negates its additive-circle character
coordinate. -/
theorem coordinateAngle_neg (b : Fin 2) (a : R) (chi : X rho) :
    coordinateAngle rho (b, -a) chi = -coordinateAngle rho (b, a) chi := by
  apply AddCircle.injective_toCircle (by norm_num)
  rw [coordinateAngle_toCircle, AddCircle.toCircle_neg,
    coordinateAngle_toCircle]
  exact coordinateCircle_neg rho b a chi

/-- Evaluation at the two unit-coefficient column roots. -/
noncomputable def scalarTorusCoordinate (chi : X rho) :
    KassabovRankZeroTorusGeometry.Torus :=
  (coordinateAngle rho (0, 1) chi, coordinateAngle rho (1, 1) chi)

theorem continuous_scalarTorusCoordinate :
    Continuous (scalarTorusCoordinate rho) :=
  (continuous_coordinateAngle rho (0, 1)).prodMk
    (continuous_coordinateAngle rho (1, 1))

/-- The scalar spectral measure pushed to the two unit-coefficient torus
coordinates. -/
noncomputable def scalarTorusMeasure (z : E) (hz : ‖z‖ = 1) :
    Measure KassabovRankZeroTorusGeometry.Torus :=
  Measure.map (scalarTorusCoordinate rho)
    (CommutativeStateSpectralMeasure.stateSpectralMeasure
      ((P rho).vectorState (Complexification.mk z 0)
        (norm_mk_zero_eq_one hz)))

noncomputable local instance scalarTorusMeasureIsFinite
    (z : E) (hz : ‖z‖ = 1) :
    IsFiniteMeasure (scalarTorusMeasure rho z hz) := by
  unfold scalarTorusMeasure
  exact Measure.isFiniteMeasure_map _ _

/-- Restricted upper conjugation has the exact shear formula on every
represented column coordinate. -/
theorem restrictUpper_coordinate (r : R) (q : Fin 2 × R) :
    restrictConjStarAlgEquiv (P rho).algebra ((P rho).rho (upperShear r))
        (upperShear_forward rho r) (upperShear_backward rho r)
        ((P rho).coordinate q) =
      if q.1 = 0 then (P rho).coordinate q
      else (P rho).coordinate (0, r * q.2) * (P rho).coordinate q := by
  apply Subtype.ext
  rw [restrictConjStarAlgEquiv_coe]
  change Unitary.conjStarAlgAut ℂ
      (Complexification E →L[ℂ] Complexification E)
      ((P rho).rho (upperShear r))
        (((P rho).rho (columnRoot q) :
          unitary (Complexification E →L[ℂ] Complexification E)) :
            Complexification E →L[ℂ] Complexification E) = _
  rw [conjStarAlgAut_representation_apply,
    upperShear_conjugate_columnRoot]
  split_ifs
  · rfl
  · rw [map_mul]
    rfl

/-- Restricted lower conjugation has the exact shear formula on every
represented column coordinate. -/
theorem restrictLower_coordinate (r : R) (q : Fin 2 × R) :
    restrictConjStarAlgEquiv (P rho).algebra ((P rho).rho (lowerShear r))
        (lowerShear_forward rho r) (lowerShear_backward rho r)
        ((P rho).coordinate q) =
      if q.1 = 1 then (P rho).coordinate q
      else (P rho).coordinate (1, r * q.2) * (P rho).coordinate q := by
  apply Subtype.ext
  rw [restrictConjStarAlgEquiv_coe]
  change Unitary.conjStarAlgAut ℂ
      (Complexification E →L[ℂ] Complexification E)
      ((P rho).rho (lowerShear r))
        (((P rho).rho (columnRoot q) :
          unitary (Complexification E →L[ℂ] Complexification E)) :
            Complexification E →L[ℂ] Complexification E) = _
  rw [conjStarAlgAut_representation_apply,
    lowerShear_conjugate_columnRoot]
  split_ifs
  · rfl
  · rw [map_mul]
    rfl

/-- The upper unit shear acts on scalar spectral coordinates as the lower
positive torus shear `(x,y) ↦ (x,x+y)`. -/
theorem scalarTorusCoordinate_characterAction_upper_one (chi : X rho) :
    scalarTorusCoordinate rho
        (characterAction (P rho).algebra ((P rho).rho (upperShear 1))
          (upperShear_forward rho 1) (upperShear_backward rho 1) chi) =
      KassabovRankZeroTorusGeometry.g21Plus
        (scalarTorusCoordinate rho chi) := by
  apply Prod.ext
  · change coordinateAngle rho (0, 1)
        (characterAction (P rho).algebra ((P rho).rho (upperShear 1))
          (upperShear_forward rho 1) (upperShear_backward rho 1) chi) =
        coordinateAngle rho (0, 1) chi
    apply AddCircle.injective_toCircle (by norm_num)
    rw [coordinateAngle_toCircle, coordinateAngle_toCircle]
    apply Circle.ext
    change characterAction (P rho).algebra ((P rho).rho (upperShear 1))
        (upperShear_forward rho 1) (upperShear_backward rho 1) chi
          ((P rho).coordinate (0, 1)) =
      chi ((P rho).coordinate (0, 1))
    rw [characterAction_apply_apply, restrictUpper_coordinate]
    simp only [Fin.isValue, if_true]
  · change coordinateAngle rho (1, 1)
        (characterAction (P rho).algebra ((P rho).rho (upperShear 1))
          (upperShear_forward rho 1) (upperShear_backward rho 1) chi) =
        coordinateAngle rho (0, 1) chi + coordinateAngle rho (1, 1) chi
    apply AddCircle.injective_toCircle (by norm_num)
    rw [coordinateAngle_toCircle, AddCircle.toCircle_add,
      coordinateAngle_toCircle, coordinateAngle_toCircle]
    apply Circle.ext
    change characterAction (P rho).algebra ((P rho).rho (upperShear 1))
        (upperShear_forward rho 1) (upperShear_backward rho 1) chi
          ((P rho).coordinate (1, 1)) =
      chi ((P rho).coordinate (0, 1)) * chi ((P rho).coordinate (1, 1))
    rw [characterAction_apply_apply, restrictUpper_coordinate]
    have hq : (((1, 1) : Fin 2 × R).1) ≠ 0 := one_ne_zero
    rw [if_neg hq, one_mul, map_mul]

/-- The lower unit shear acts on scalar spectral coordinates as the upper
positive torus shear `(x,y) ↦ (x+y,y)`. -/
theorem scalarTorusCoordinate_characterAction_lower_one (chi : X rho) :
    scalarTorusCoordinate rho
        (characterAction (P rho).algebra ((P rho).rho (lowerShear 1))
          (lowerShear_forward rho 1) (lowerShear_backward rho 1) chi) =
      KassabovRankZeroTorusGeometry.g12Plus
        (scalarTorusCoordinate rho chi) := by
  apply Prod.ext
  · change coordinateAngle rho (0, 1)
        (characterAction (P rho).algebra ((P rho).rho (lowerShear 1))
          (lowerShear_forward rho 1) (lowerShear_backward rho 1) chi) =
        coordinateAngle rho (0, 1) chi + coordinateAngle rho (1, 1) chi
    apply AddCircle.injective_toCircle (by norm_num)
    rw [coordinateAngle_toCircle, AddCircle.toCircle_add,
      coordinateAngle_toCircle, coordinateAngle_toCircle]
    apply Circle.ext
    change characterAction (P rho).algebra ((P rho).rho (lowerShear 1))
        (lowerShear_forward rho 1) (lowerShear_backward rho 1) chi
          ((P rho).coordinate (0, 1)) =
      chi ((P rho).coordinate (0, 1)) * chi ((P rho).coordinate (1, 1))
    rw [characterAction_apply_apply, restrictLower_coordinate]
    have hq : (((0, 1) : Fin 2 × R).1) ≠ 1 := zero_ne_one
    rw [if_neg hq, one_mul, map_mul]
    exact
      (mul_comm (chi ((P rho).coordinate (1, 1)))
        (chi ((P rho).coordinate (0, 1))))
  · change coordinateAngle rho (1, 1)
        (characterAction (P rho).algebra ((P rho).rho (lowerShear 1))
          (lowerShear_forward rho 1) (lowerShear_backward rho 1) chi) =
        coordinateAngle rho (1, 1) chi
    apply AddCircle.injective_toCircle (by norm_num)
    rw [coordinateAngle_toCircle, coordinateAngle_toCircle]
    apply Circle.ext
    change characterAction (P rho).algebra ((P rho).rho (lowerShear 1))
        (lowerShear_forward rho 1) (lowerShear_backward rho 1) chi
          ((P rho).coordinate (1, 1)) =
      chi ((P rho).coordinate (1, 1))
    rw [characterAction_apply_apply, restrictLower_coordinate]
    simp only [Fin.isValue, if_true]

private theorem upperNegOne_eval_zero (chi : X rho) :
    characterAction (P rho).algebra ((P rho).rho (upperShear (-1)))
        (upperShear_forward rho (-1)) (upperShear_backward rho (-1)) chi
          ((P rho).coordinate (0, 1)) =
      chi ((P rho).coordinate (0, 1)) := by
  rw [characterAction_apply_apply, restrictUpper_coordinate]
  simp only [Fin.isValue, if_true]

private theorem upperNegOne_eval_one (chi : X rho) :
    characterAction (P rho).algebra ((P rho).rho (upperShear (-1)))
        (upperShear_forward rho (-1)) (upperShear_backward rho (-1)) chi
          ((P rho).coordinate (1, 1)) =
      chi ((P rho).coordinate (0, -1)) *
        chi ((P rho).coordinate (1, 1)) := by
  rw [characterAction_apply_apply, restrictUpper_coordinate]
  have hq : (((1, 1) : Fin 2 × R).1) ≠ 0 := one_ne_zero
  rw [if_neg hq, neg_mul, one_mul, map_mul]

private theorem lowerNegOne_eval_zero (chi : X rho) :
    characterAction (P rho).algebra ((P rho).rho (lowerShear (-1)))
        (lowerShear_forward rho (-1)) (lowerShear_backward rho (-1)) chi
          ((P rho).coordinate (0, 1)) =
      chi ((P rho).coordinate (1, -1)) *
        chi ((P rho).coordinate (0, 1)) := by
  rw [characterAction_apply_apply, restrictLower_coordinate]
  have hq : (((0, 1) : Fin 2 × R).1) ≠ 1 := zero_ne_one
  rw [if_neg hq, neg_mul, one_mul, map_mul]

private theorem lowerNegOne_eval_one (chi : X rho) :
    characterAction (P rho).algebra ((P rho).rho (lowerShear (-1)))
        (lowerShear_forward rho (-1)) (lowerShear_backward rho (-1)) chi
          ((P rho).coordinate (1, 1)) =
      chi ((P rho).coordinate (1, 1)) := by
  rw [characterAction_apply_apply, restrictLower_coordinate]
  simp only [Fin.isValue, if_true]

private theorem upperNegOne_circle_zero (chi : X rho) :
    coordinateCircle rho (0, 1)
        (characterAction (P rho).algebra ((P rho).rho (upperShear (-1)))
          (upperShear_forward rho (-1)) (upperShear_backward rho (-1)) chi) =
      coordinateCircle rho (0, 1) chi := by
  apply Circle.ext
  exact upperNegOne_eval_zero rho chi

private theorem upperNegOne_circle_one (chi : X rho) :
    coordinateCircle rho (1, 1)
        (characterAction (P rho).algebra ((P rho).rho (upperShear (-1)))
          (upperShear_forward rho (-1)) (upperShear_backward rho (-1)) chi) =
      coordinateCircle rho (0, -1) chi * coordinateCircle rho (1, 1) chi := by
  apply Circle.ext
  exact upperNegOne_eval_one rho chi

private theorem lowerNegOne_circle_zero (chi : X rho) :
    coordinateCircle rho (0, 1)
        (characterAction (P rho).algebra ((P rho).rho (lowerShear (-1)))
          (lowerShear_forward rho (-1)) (lowerShear_backward rho (-1)) chi) =
      coordinateCircle rho (1, -1) chi * coordinateCircle rho (0, 1) chi := by
  apply Circle.ext
  exact lowerNegOne_eval_zero rho chi

private theorem lowerNegOne_circle_one (chi : X rho) :
    coordinateCircle rho (1, 1)
        (characterAction (P rho).algebra ((P rho).rho (lowerShear (-1)))
          (lowerShear_forward rho (-1)) (lowerShear_backward rho (-1)) chi) =
      coordinateCircle rho (1, 1) chi := by
  apply Circle.ext
  exact lowerNegOne_eval_one rho chi

private theorem upperNegOne_angle_zero (chi : X rho) :
    coordinateAngle rho (0, 1)
        (characterAction (P rho).algebra ((P rho).rho (upperShear (-1)))
          (upperShear_forward rho (-1)) (upperShear_backward rho (-1)) chi) =
      coordinateAngle rho (0, 1) chi := by
  apply AddCircle.injective_toCircle (by norm_num)
  rw [coordinateAngle_toCircle, coordinateAngle_toCircle]
  exact upperNegOne_circle_zero rho chi

private theorem upperNegOne_angle_one (chi : X rho) :
    coordinateAngle rho (1, 1)
        (characterAction (P rho).algebra ((P rho).rho (upperShear (-1)))
          (upperShear_forward rho (-1)) (upperShear_backward rho (-1)) chi) =
      coordinateAngle rho (0, -1) chi + coordinateAngle rho (1, 1) chi := by
  apply AddCircle.injective_toCircle (by norm_num)
  rw [coordinateAngle_toCircle, AddCircle.toCircle_add,
    coordinateAngle_toCircle, coordinateAngle_toCircle]
  exact upperNegOne_circle_one rho chi

private theorem lowerNegOne_angle_zero (chi : X rho) :
    coordinateAngle rho (0, 1)
        (characterAction (P rho).algebra ((P rho).rho (lowerShear (-1)))
          (lowerShear_forward rho (-1)) (lowerShear_backward rho (-1)) chi) =
      coordinateAngle rho (1, -1) chi + coordinateAngle rho (0, 1) chi := by
  apply AddCircle.injective_toCircle (by norm_num)
  rw [coordinateAngle_toCircle, AddCircle.toCircle_add,
    coordinateAngle_toCircle, coordinateAngle_toCircle]
  exact lowerNegOne_circle_zero rho chi

private theorem lowerNegOne_angle_one (chi : X rho) :
    coordinateAngle rho (1, 1)
        (characterAction (P rho).algebra ((P rho).rho (lowerShear (-1)))
          (lowerShear_forward rho (-1)) (lowerShear_backward rho (-1)) chi) =
      coordinateAngle rho (1, 1) chi := by
  apply AddCircle.injective_toCircle (by norm_num)
  rw [coordinateAngle_toCircle, coordinateAngle_toCircle]
  exact lowerNegOne_circle_one rho chi

/-- The upper negative unit shear acts on scalar spectral coordinates as
`(x,y) ↦ (x,y-x)`. -/
theorem scalarTorusCoordinate_characterAction_upper_neg_one (chi : X rho) :
    scalarTorusCoordinate rho
        (characterAction (P rho).algebra ((P rho).rho (upperShear (-1)))
          (upperShear_forward rho (-1)) (upperShear_backward rho (-1)) chi) =
      KassabovRankZeroTorusGeometry.g21Minus
        (scalarTorusCoordinate rho chi) := by
  apply Prod.ext
  · exact upperNegOne_angle_zero rho chi
  · change coordinateAngle rho (1, 1)
        (characterAction (P rho).algebra ((P rho).rho (upperShear (-1)))
          (upperShear_forward rho (-1)) (upperShear_backward rho (-1)) chi) =
        coordinateAngle rho (1, 1) chi - coordinateAngle rho (0, 1) chi
    rw [upperNegOne_angle_one rho chi, coordinateAngle_neg, sub_eq_add_neg]
    exact add_comm _ _

/-- The lower negative unit shear acts on scalar spectral coordinates as
`(x,y) ↦ (x-y,y)`. -/
theorem scalarTorusCoordinate_characterAction_lower_neg_one (chi : X rho) :
    scalarTorusCoordinate rho
        (characterAction (P rho).algebra ((P rho).rho (lowerShear (-1)))
          (lowerShear_forward rho (-1)) (lowerShear_backward rho (-1)) chi) =
      KassabovRankZeroTorusGeometry.g12Minus
        (scalarTorusCoordinate rho chi) := by
  apply Prod.ext
  · change coordinateAngle rho (0, 1)
        (characterAction (P rho).algebra ((P rho).rho (lowerShear (-1)))
          (lowerShear_forward rho (-1)) (lowerShear_backward rho (-1)) chi) =
        coordinateAngle rho (0, 1) chi - coordinateAngle rho (1, 1) chi
    rw [lowerNegOne_angle_zero rho chi, coordinateAngle_neg, sub_eq_add_neg]
    exact add_comm _ _
  · exact lowerNegOne_angle_one rho chi

/-! ### Quasi-invariance of the pushed scalar torus measure -/

variable (Generators : Type u) [Fintype Generators]

/-- The pushed scalar measure is quadratically quasi-invariant under
`(x,y) ↦ (x,x+y)`. -/
theorem scalarTorusMeasure_measurableQuasiInvariantAtScale_g21Plus
    (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ Generators) →*
      (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1) (delta : ℝ) (hdelta : 0 < delta)
    (hnear : ∀ s ∈ integralControlSet Generators, ‖rho s z - z‖ < delta) :
    KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
      (scalarTorusMeasure rho z hz) delta
      KassabovRankZeroTorusGeometry.g21Plus := by
  apply measurableQuasiInvariantAtScale_map_of_semiconj
    (CommutativeStateSpectralMeasure.stateSpectralMeasure
      ((P rho).vectorState (Complexification.mk z 0)
        (norm_mk_zero_eq_one hz))) delta
    (scalarTorusCoordinate rho) (continuous_scalarTorusCoordinate rho).measurable
    (CommutativeCStarCovariance.characterHomeomorph (P rho).algebra
      ((P rho).rho (upperShear 1))
      (upperShear_forward rho 1) (upperShear_backward rho 1)).toMeasurableEquiv
    KassabovRankZeroTorusGeometry.measurableEquivG21Plus
  · exact scalarTorusCoordinate_characterAction_upper_one rho
  · simpa [integralControlCoefficient] using
      upperShear_measurableQuasiInvariantAtScale Generators rho z hz delta
        hdelta hnear none

/-- The pushed scalar measure is quadratically quasi-invariant under
`(x,y) ↦ (x,y-x)`. -/
theorem scalarTorusMeasure_measurableQuasiInvariantAtScale_g21Minus
    (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ Generators) →*
      (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1) (delta : ℝ) (hdelta : 0 < delta)
    (hnear : ∀ s ∈ integralControlSet Generators, ‖rho s z - z‖ < delta) :
    KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
      (scalarTorusMeasure rho z hz) delta
      KassabovRankZeroTorusGeometry.g21Minus := by
  apply measurableQuasiInvariantAtScale_map_of_semiconj
    (CommutativeStateSpectralMeasure.stateSpectralMeasure
      ((P rho).vectorState (Complexification.mk z 0)
        (norm_mk_zero_eq_one hz))) delta
    (scalarTorusCoordinate rho) (continuous_scalarTorusCoordinate rho).measurable
    (CommutativeCStarCovariance.characterHomeomorph (P rho).algebra
      ((P rho).rho (upperShear (-1)))
      (upperShear_forward rho (-1))
      (upperShear_backward rho (-1))).toMeasurableEquiv
    KassabovRankZeroTorusGeometry.measurableEquivG21Minus
  · exact scalarTorusCoordinate_characterAction_upper_neg_one rho
  · exact upperShear_neg_one_measurableQuasiInvariantAtScale
      Generators rho z hz delta hdelta hnear

/-- The pushed scalar measure is quadratically quasi-invariant under
`(x,y) ↦ (x+y,y)`. -/
theorem scalarTorusMeasure_measurableQuasiInvariantAtScale_g12Plus
    (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ Generators) →*
      (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1) (delta : ℝ) (hdelta : 0 < delta)
    (hnear : ∀ s ∈ integralControlSet Generators, ‖rho s z - z‖ < delta) :
    KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
      (scalarTorusMeasure rho z hz) delta
      KassabovRankZeroTorusGeometry.g12Plus := by
  apply measurableQuasiInvariantAtScale_map_of_semiconj
    (CommutativeStateSpectralMeasure.stateSpectralMeasure
      ((P rho).vectorState (Complexification.mk z 0)
        (norm_mk_zero_eq_one hz))) delta
    (scalarTorusCoordinate rho) (continuous_scalarTorusCoordinate rho).measurable
    (CommutativeCStarCovariance.characterHomeomorph (P rho).algebra
      ((P rho).rho (lowerShear 1))
      (lowerShear_forward rho 1) (lowerShear_backward rho 1)).toMeasurableEquiv
    KassabovRankZeroTorusGeometry.measurableEquivG12Plus
  · exact scalarTorusCoordinate_characterAction_lower_one rho
  · simpa [integralControlCoefficient] using
      lowerShear_measurableQuasiInvariantAtScale Generators rho z hz delta
        hdelta hnear none

/-- The pushed scalar measure is quadratically quasi-invariant under
`(x,y) ↦ (x-y,y)`. -/
theorem scalarTorusMeasure_measurableQuasiInvariantAtScale_g12Minus
    (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ Generators) →*
      (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1) (delta : ℝ) (hdelta : 0 < delta)
    (hnear : ∀ s ∈ integralControlSet Generators, ‖rho s z - z‖ < delta) :
    KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
      (scalarTorusMeasure rho z hz) delta
      KassabovRankZeroTorusGeometry.g12Minus := by
  apply measurableQuasiInvariantAtScale_map_of_semiconj
    (CommutativeStateSpectralMeasure.stateSpectralMeasure
      ((P rho).vectorState (Complexification.mk z 0)
        (norm_mk_zero_eq_one hz))) delta
    (scalarTorusCoordinate rho) (continuous_scalarTorusCoordinate rho).measurable
    (CommutativeCStarCovariance.characterHomeomorph (P rho).algebra
      ((P rho).rho (lowerShear (-1)))
      (lowerShear_forward rho (-1))
      (lowerShear_backward rho (-1))).toMeasurableEquiv
    KassabovRankZeroTorusGeometry.measurableEquivG12Minus
  · exact scalarTorusCoordinate_characterAction_lower_neg_one rho
  · exact lowerShear_neg_one_measurableQuasiInvariantAtScale
      Generators rho z hz delta hdelta hnear

/-- Closed package of the four torus shear estimates obtained from the
integral control set. -/
def IntegralScalarTorusFourShearQuasiInvariance : Prop :=
  ∀ (Generators E : Type) [Fintype Generators]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ Generators) →*
      (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1) (delta : ℝ),
    0 < delta →
    (∀ s ∈ integralControlSet Generators, ‖rho s z - z‖ < delta) →
    KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
        (scalarTorusMeasure rho z hz) delta
        KassabovRankZeroTorusGeometry.g21Plus ∧
      KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
        (scalarTorusMeasure rho z hz) delta
        KassabovRankZeroTorusGeometry.g21Minus ∧
      KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
        (scalarTorusMeasure rho z hz) delta
        KassabovRankZeroTorusGeometry.g12Plus ∧
      KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale
        (scalarTorusMeasure rho z hz) delta
        KassabovRankZeroTorusGeometry.g12Minus

/-- The exact spectral construction supplies all four torus shear estimates
without an additional analytic premise. -/
theorem integralScalarTorusFourShearQuasiInvariance :
    IntegralScalarTorusFourShearQuasiInvariance := by
  intro Generators E _ _ _ _ rho z hz delta hdelta hnear
  exact ⟨
    scalarTorusMeasure_measurableQuasiInvariantAtScale_g21Plus
      Generators rho z hz delta hdelta hnear,
    scalarTorusMeasure_measurableQuasiInvariantAtScale_g21Minus
      Generators rho z hz delta hdelta hnear,
    scalarTorusMeasure_measurableQuasiInvariantAtScale_g12Plus
      Generators rho z hz delta hdelta hnear,
    scalarTorusMeasure_measurableQuasiInvariantAtScale_g12Minus
      Generators rho z hz delta hdelta hnear⟩

#audit_closed_axioms integralScalarTorusFourShearQuasiInvariance

end
end IntegralColumnPlaneSpectralTorus
end GroupApproximation
