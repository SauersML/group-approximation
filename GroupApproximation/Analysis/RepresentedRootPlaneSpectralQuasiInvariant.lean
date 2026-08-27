import GroupApproximation.Analysis.CommutativeCStarCovariance
import GroupApproximation.Analysis.HilbertQuadraticTransport
import GroupApproximation.Analysis.RepresentedRootPlaneSpectralMeasure
import GroupApproximation.PropertyT.KassabovBorelMeasureInequalities
import Mathlib.Topology.UrysohnsLemma

/-!
# Quasi-invariance of a represented root-plane spectral measure

This file passes from displacement of a vector by a normalizing unitary to
Kassabov's measurable quadratic quasi-invariance estimate for the scalar RMK
spectral measure.  The passage from continuous functions to Borel sets uses
regularity on both sides: compact subsets, open supersets, and a Urysohn
cutoff.  No projection-valued measure or measurability of arbitrary subsets
is assumed.
-/

namespace GroupApproximation

namespace RepresentedRootPlaneSpectralQuasiInvariant

open CStarState WeakDual MeasureTheory Set
open scoped InnerProductSpace

universe u v w

/-! ### Continuous cutoffs and regular measures -/

section RegularMeasures

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A continuous-cutoff quadratic estimate extends to every measurable set
for finite regular Borel measures. -/
theorem abs_measureReal_sub_le_of_continuous_cutoff_bound
    (mu nu : Measure X) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    [mu.Regular] [nu.Regular] {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (htest : ∀ f : CompactlySupportedContinuousMap X ℝ,
      (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
      |∫ x, f x ∂nu - ∫ x, f x ∂mu| ≤
        2 * epsilon * Real.sqrt (∫ x, f x ∂mu) + epsilon ^ 2)
    (A : Set X) (hA : MeasurableSet A) :
    |nu.real A - mu.real A| ≤
      2 * epsilon * Real.sqrt (mu.real A) + epsilon ^ 2 := by
  refine le_of_forall_pos_le_add fun r hr ↦ ?_
  let t : ℝ := min 1 (r / (4 * (epsilon + 1)))
  have hepsilonOne : 0 < epsilon + 1 := by linarith
  have hdenom : 0 < 4 * (epsilon + 1) := mul_pos (by norm_num) hepsilonOne
  have htpos : 0 < t := by
    exact lt_min (by norm_num) (div_pos hr hdenom)
  have htOne : t ≤ 1 := min_le_left _ _
  have htRatio : t ≤ r / (4 * (epsilon + 1)) := min_le_right _ _
  let delta : ℝ := t ^ 2
  have hdelta : 0 < delta := sq_pos_of_pos htpos
  let d : NNReal := ⟨delta, hdelta.le⟩
  have hd : (d : ENNReal) ≠ 0 := by
    apply ENNReal.coe_ne_zero.mpr
    apply NNReal.coe_ne_zero.mp
    change delta ≠ 0
    exact hdelta.ne'
  obtain ⟨Kmu, hKmuA, hKmuCompact, hmuInner⟩ :=
    hA.exists_isCompact_lt_add (measure_ne_top mu A) hd
  obtain ⟨Knu, hKnuA, hKnuCompact, hnuInner⟩ :=
    hA.exists_isCompact_lt_add (measure_ne_top nu A) hd
  obtain ⟨Umu, hAUmu, hUmuOpen, hmuOuter⟩ :=
    A.exists_isOpen_lt_add (measure_ne_top mu A) hd
  obtain ⟨Unu, hAUnu, hUnuOpen, hnuOuter⟩ :=
    A.exists_isOpen_lt_add (measure_ne_top nu A) hd
  let K : Set X := Kmu ∪ Knu
  let V : Set X := Umu ∩ Unu
  have hKCompact : IsCompact K := hKmuCompact.union hKnuCompact
  have hVOpen : IsOpen V := hUmuOpen.inter hUnuOpen
  have hKV : K ⊆ V := by
    exact union_subset (hKmuA.trans (subset_inter hAUmu hAUnu))
      (hKnuA.trans (subset_inter hAUmu hAUnu))
  obtain ⟨f, hfOne, hfCompact, hfSupport, hfIcc⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      hKCompact hVOpen hKV
  let fc : CompactlySupportedContinuousMap X ℝ :=
    ⟨f, hasCompactSupport_def.mpr hfCompact⟩
  have hmuInnerReal : mu.real A ≤ mu.real Kmu + delta := by
    have h := hmuInner.le
    have h' : (mu A).toReal ≤ (mu Kmu + (d : ENNReal)).toReal :=
      (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr h
    rw [ENNReal.toReal_add] at h'
    · change (mu A).toReal ≤ (mu Kmu).toReal + delta at h'
      simpa only [measureReal_def] using h'
    all_goals finiteness
  have hnuInnerReal : nu.real A ≤ nu.real Knu + delta := by
    have h := hnuInner.le
    have h' : (nu A).toReal ≤ (nu Knu + (d : ENNReal)).toReal :=
      (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr h
    rw [ENNReal.toReal_add] at h'
    · change (nu A).toReal ≤ (nu Knu).toReal + delta at h'
      simpa only [measureReal_def] using h'
    all_goals finiteness
  have hmuOuterReal : mu.real V ≤ mu.real A + delta := by
    have hVmu : V ⊆ Umu := inter_subset_left
    have h := (measure_mono hVmu).trans hmuOuter.le
    have h' : (mu V).toReal ≤ (mu A + (d : ENNReal)).toReal :=
      (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr h
    rw [ENNReal.toReal_add] at h'
    · change (mu V).toReal ≤ (mu A).toReal + delta at h'
      simpa only [measureReal_def] using h'
    all_goals finiteness
  have hnuOuterReal : nu.real V ≤ nu.real A + delta := by
    have hVnu : V ⊆ Unu := inter_subset_right
    have h := (measure_mono hVnu).trans hnuOuter.le
    have h' : (nu V).toReal ≤ (nu A + (d : ENNReal)).toReal :=
      (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr h
    rw [ENNReal.toReal_add] at h'
    · change (nu V).toReal ≤ (nu A).toReal + delta at h'
      simpa only [measureReal_def] using h'
    all_goals finiteness
  have hKmuIntegral : mu.real Kmu ≤ ∫ x, fc x ∂mu := by
    calc
      mu.real Kmu = ∫ x, Kmu.indicator 1 x ∂mu :=
        (integral_indicator_one hKmuCompact.measurableSet).symm
      _ ≤ ∫ x, fc x ∂mu := by
        refine integral_mono ?_ fc.integrable ?_
        · exact IntegrableOn.integrable_indicator integrableOn_const
            hKmuCompact.measurableSet
        · intro x
          by_cases hx : x ∈ Kmu
          · have hxK : x ∈ K := Or.inl hx
            simp [hx, fc, hfOne hxK]
          · simp [hx, fc, (hfIcc x).1]
  have hKnuIntegral : nu.real Knu ≤ ∫ x, fc x ∂nu := by
    calc
      nu.real Knu = ∫ x, Knu.indicator 1 x ∂nu :=
        (integral_indicator_one hKnuCompact.measurableSet).symm
      _ ≤ ∫ x, fc x ∂nu := by
        refine integral_mono ?_ fc.integrable ?_
        · exact IntegrableOn.integrable_indicator integrableOn_const
            hKnuCompact.measurableSet
        · intro x
          by_cases hx : x ∈ Knu
          · have hxK : x ∈ K := Or.inr hx
            simp [hx, fc, hfOne hxK]
          · simp [hx, fc, (hfIcc x).1]
  have hIntegralMuV : ∫ x, fc x ∂mu ≤ mu.real V := by
    calc
      ∫ x, fc x ∂mu ≤ ∫ x, V.indicator 1 x ∂mu := by
        refine integral_mono fc.integrable ?_ ?_
        · exact IntegrableOn.integrable_indicator integrableOn_const
            hVOpen.measurableSet
        · intro x
          by_cases hx : x ∈ tsupport f
          · simp [fc, (hfSupport hx), (hfIcc x).2]
          · simp [fc, image_eq_zero_of_notMem_tsupport hx,
              Set.indicator_nonneg]
      _ = mu.real V := integral_indicator_one hVOpen.measurableSet
  have hIntegralNuV : ∫ x, fc x ∂nu ≤ nu.real V := by
    calc
      ∫ x, fc x ∂nu ≤ ∫ x, V.indicator 1 x ∂nu := by
        refine integral_mono fc.integrable ?_ ?_
        · exact IntegrableOn.integrable_indicator integrableOn_const
            hVOpen.measurableSet
        · intro x
          by_cases hx : x ∈ tsupport f
          · simp [fc, (hfSupport hx), (hfIcc x).2]
          · simp [fc, image_eq_zero_of_notMem_tsupport hx,
              Set.indicator_nonneg]
      _ = nu.real V := integral_indicator_one hVOpen.measurableSet
  have hmuLower : mu.real A ≤ ∫ x, fc x ∂mu + delta := by
    linarith
  have hnuLower : nu.real A ≤ ∫ x, fc x ∂nu + delta := by
    linarith
  have hmuUpper : ∫ x, fc x ∂mu ≤ mu.real A + delta := by
    linarith
  have hnuUpper : ∫ x, fc x ∂nu ≤ nu.real A + delta := by
    linarith
  have htestBound := htest fc hfIcc
  have hsqrtUpper :
      Real.sqrt (∫ x, fc x ∂mu) ≤
        Real.sqrt (mu.real A) + Real.sqrt delta := by
    refine (Real.sqrt_le_sqrt hmuUpper).trans ?_
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · rw [add_sq, Real.sq_sqrt measureReal_nonneg,
          Real.sq_sqrt hdelta.le]
      nlinarith [Real.sqrt_nonneg (mu.real A), Real.sqrt_nonneg delta]
  have hsqrtScaled :
      2 * epsilon * Real.sqrt (∫ x, fc x ∂mu) ≤
        2 * epsilon *
          (Real.sqrt (mu.real A) + Real.sqrt delta) :=
    mul_le_mul_of_nonneg_left hsqrtUpper
      (mul_nonneg (by norm_num) hepsilon)
  have hsqrtDelta : Real.sqrt delta = t := by
    change Real.sqrt (t ^ 2) = t
    rw [Real.sqrt_sq_eq_abs, abs_of_pos htpos]
  have htMul : t * (4 * (epsilon + 1)) ≤ r :=
    (le_div_iff₀ hdenom).mp htRatio
  have htSq : t ^ 2 ≤ t := by nlinarith
  have herror : 2 * delta + 2 * epsilon * Real.sqrt delta ≤ r := by
    change 2 * t ^ 2 + 2 * epsilon * Real.sqrt (t ^ 2) ≤ r
    rw [Real.sqrt_sq_eq_abs, abs_of_pos htpos]
    nlinarith
  rw [abs_le] at htestBound ⊢
  constructor <;> linarith

end RegularMeasures

/-! ### Vector-state cutoff estimates -/

section VectorState

variable {A : Type u} [CommCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

local notation "X" => characterSpace ℂ A

noncomputable local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

/-- The vector state of a positive square is the squared norm of the
represented vector.  This local calculation keeps the quasi-invariance
module independent of the concrete root-plane coordinate used later. -/
private theorem stateOfVector_star_mul_self_re
    (pi : CStarTensor.StarRep A H) (x : H) (hx : ‖x‖ = 1) (b : A) :
    ((CStarTensor.stateOfVector pi x hx).toCLM (star b * b)).re =
      ‖pi.hom b x‖ ^ 2 := by
  rw [CStarTensor.stateOfVector_apply, ← CStarTensor.re_inner_self]
  have hmul : pi.hom (star b * b) x =
      pi.hom (star b) (pi.hom b x) := by
    rw [map_mul]
    rfl
  rw [hmul]
  exact congrArg Complex.re
    ((pi.isAdjoint_star b x (pi.hom b x)).symm)

/-- A positive continuous cutoff is represented by a contraction on every
star-representation, and hence its two vector-state integrals satisfy the
quadratic transport estimate. -/
theorem abs_integral_stateSpectralMeasure_sub_le
    (pi : CStarTensor.StarRep A H)
    (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hxy : ‖y - x‖ ≤ epsilon)
    (f : CompactlySupportedContinuousMap X ℝ)
    (hf : ∀ chi, f chi ∈ Set.Icc (0 : ℝ) 1) :
    |∫ chi, f chi
          ∂CommutativeStateSpectralMeasure.stateSpectralMeasure
            (CStarTensor.stateOfVector pi y hy) -
       ∫ chi, f chi
          ∂CommutativeStateSpectralMeasure.stateSpectralMeasure
            (CStarTensor.stateOfVector pi x hx)| ≤
      2 * epsilon * Real.sqrt
        (∫ chi, f chi
          ∂CommutativeStateSpectralMeasure.stateSpectralMeasure
            (CStarTensor.stateOfVector pi x hx)) + epsilon ^ 2 := by
  let q : CompactlySupportedContinuousMap X ℝ :=
    { toFun := fun chi ↦ Real.sqrt (f chi)
      continuous_toFun := Real.continuous_sqrt.comp f.continuous_toFun
      hasCompactSupport' := HasCompactSupport.of_compactSpace _ }
  let b : A := CommutativeStateSpectralMeasure.spectralLift q
  let T : H →L[ℂ] H := pi.hom b
  have hfun :
      CommutativeStateSpectralMeasure.complexifyRealFunction f =
        star (CommutativeStateSpectralMeasure.complexifyRealFunction q) *
          CommutativeStateSpectralMeasure.complexifyRealFunction q := by
    ext chi
    have hsqrt := Real.sq_sqrt (hf chi).1
    change (f chi : ℂ) =
      star (Real.sqrt (f chi) : ℂ) * (Real.sqrt (f chi) : ℂ)
    simpa [Complex.star_def, pow_two] using
      congrArg (fun z : ℝ ↦ (z : ℂ)) hsqrt.symm
  have hbSq : CommutativeStateSpectralMeasure.spectralLift f = star b * b := by
    unfold b CommutativeStateSpectralMeasure.spectralLift
    rw [hfun, map_mul, map_star]
  have hT : ‖T‖ ≤ 1 := by
    calc
      ‖T‖ ≤ ‖b‖ := NonUnitalStarAlgHom.norm_apply_le pi.toStarAlgHom b
      _ = ‖CommutativeStateSpectralMeasure.complexifyRealFunction q‖ := by
        unfold b CommutativeStateSpectralMeasure.spectralLift
        exact StarAlgEquiv.norm_map _ _
      _ ≤ 1 := by
        rw [ContinuousMap.norm_le _ (by norm_num)]
        intro chi
        change ‖(Real.sqrt (f chi) : ℂ)‖ ≤ 1
        simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using
          (Real.sqrt_le_one.mpr (hf chi).2)
  have hIntX :
      ∫ chi, f chi
          ∂CommutativeStateSpectralMeasure.stateSpectralMeasure
            (CStarTensor.stateOfVector pi x hx) = ‖T x‖ ^ 2 := by
    rw [CommutativeStateSpectralMeasure.integral_stateSpectralMeasure, hbSq]
    exact stateOfVector_star_mul_self_re pi x hx b
  have hIntY :
      ∫ chi, f chi
          ∂CommutativeStateSpectralMeasure.stateSpectralMeasure
            (CStarTensor.stateOfVector pi y hy) = ‖T y‖ ^ 2 := by
    rw [CommutativeStateSpectralMeasure.integral_stateSpectralMeasure, hbSq]
    exact stateOfVector_star_mul_self_re pi y hy b
  rw [hIntX, hIntY]
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg (T x))] using
    HilbertQuadraticTransport.abs_norm_apply_sq_sub_le_of_norm_le_one_of_norm_sub_le
      T x y epsilon hT hepsilon hxy

/-- The scalar RMK measures of two nearby unit vectors satisfy Kassabov's
quadratic estimate on every Borel set. -/
theorem abs_measureReal_stateSpectralMeasure_sub_le
    (pi : CStarTensor.StarRep A H)
    (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hxy : ‖y - x‖ ≤ epsilon)
    (B : Set X) (hB : MeasurableSet B) :
    |(CommutativeStateSpectralMeasure.stateSpectralMeasure
          (CStarTensor.stateOfVector pi y hy)).real B -
       (CommutativeStateSpectralMeasure.stateSpectralMeasure
          (CStarTensor.stateOfVector pi x hx)).real B| ≤
      2 * epsilon * Real.sqrt
        ((CommutativeStateSpectralMeasure.stateSpectralMeasure
          (CStarTensor.stateOfVector pi x hx)).real B) + epsilon ^ 2 := by
  exact abs_measureReal_sub_le_of_continuous_cutoff_bound
    (CommutativeStateSpectralMeasure.stateSpectralMeasure
      (CStarTensor.stateOfVector pi x hx))
    (CommutativeStateSpectralMeasure.stateSpectralMeasure
      (CStarTensor.stateOfVector pi y hy)) hepsilon
    (abs_integral_stateSpectralMeasure_sub_le pi x y hx hy hepsilon hxy) B hB

end VectorState

/-! ### Covariance and the normalizing unitary -/

section Plane

variable {G : Type u} [Group G] {I : Type v}
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

open CommutativeCStarCovariance
open RepresentedRootPlaneSpectralMeasure
open KassabovBorelMeasureInequalities

variable (P : RepresentedAbelianPlane G I H)

local notation "S" => P.algebra
local notation "X" => characterSpace ℂ S

noncomputable local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

/-- Pull a real compactly supported continuous function back along a
homeomorphism. -/
noncomputable def pullbackRealFunction (e : X ≃ₜ X)
    (f : CompactlySupportedContinuousMap X ℝ) :
    CompactlySupportedContinuousMap X ℝ where
  toFun chi := f (e chi)
  continuous_toFun := f.continuous_toFun.comp e.continuous
  hasCompactSupport' := HasCompactSupport.of_compactSpace _

@[simp] theorem pullbackRealFunction_apply (e : X ≃ₜ X)
    (f : CompactlySupportedContinuousMap X ℝ) (chi : X) :
    pullbackRealFunction P e f chi = f (e chi) := rfl

/-- The inverse character action and inverse restricted conjugation commute
with the inverse Gelfand transform. -/
theorem spectralLift_pullback_characterHomeomorph_symm
    (u : unitary (H →L[ℂ] H))
    (hforward : ∀ x : S,
      Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u x.1 ∈ S)
    (hbackward : ∀ x : S,
      (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u).symm x.1 ∈ S)
    (f : CompactlySupportedContinuousMap X ℝ) :
    CommutativeStateSpectralMeasure.spectralLift
        (pullbackRealFunction P
          (characterHomeomorph S u hforward hbackward).symm f) =
      (restrictConjStarAlgEquiv S u hforward hbackward).symm
      (CommutativeStateSpectralMeasure.spectralLift f) := by
  apply (gelfandStarTransform S).injective
  have hleft :
      (gelfandStarTransform S).toRingEquiv
          (CommutativeStateSpectralMeasure.spectralLift
            (pullbackRealFunction P
              (characterHomeomorph S u hforward hbackward).symm f)) =
        CommutativeStateSpectralMeasure.complexifyRealFunction
          (pullbackRealFunction P
            (characterHomeomorph S u hforward hbackward).symm f) :=
    (gelfandStarTransform S).apply_symm_apply _
  rw [hleft]
  apply ContinuousMap.ext
  intro chi
  have hGelfand :
      (gelfandStarTransform S)
          (CommutativeStateSpectralMeasure.spectralLift f) =
        CommutativeStateSpectralMeasure.complexifyRealFunction f :=
    (gelfandStarTransform S).apply_symm_apply
      (CommutativeStateSpectralMeasure.complexifyRealFunction f)
  -- One `change`, not two.  This proof used to pass through an intermediate
  -- form that nothing then referred to, and each `change` is a full defeq check
  -- of the whole goal against a large pattern over the Gelfand transform and
  -- the restricted conjugation.  Defeq is transitive, so the first was pure
  -- cost.
  change (f ((characterHomeomorph S u hforward hbackward).symm chi) : ℂ) =
    ((gelfandStarTransform S)
      (CommutativeStateSpectralMeasure.spectralLift f))
        ((characterHomeomorph S u hforward hbackward).symm chi)
  rw [hGelfand]
  rfl

/-- Mapping a vector-state spectral measure by the inverse character action
is exactly the spectral measure of the moved vector. -/
theorem map_characterHomeomorph_symm_stateSpectralMeasure
    (zeta : H) (hzeta : ‖zeta‖ = 1)
    (u : unitary (H →L[ℂ] H))
    (hforward : ∀ x : S,
      Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u x.1 ∈ S)
    (hbackward : ∀ x : S,
      (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u).symm x.1 ∈ S) :
    Measure.map (characterHomeomorph S u hforward hbackward).symm
        (CommutativeStateSpectralMeasure.stateSpectralMeasure
          (P.vectorState zeta hzeta)) =
      CommutativeStateSpectralMeasure.stateSpectralMeasure
        (P.vectorState ((u : H →L[ℂ] H) zeta)
          (by rw [Unitary.norm_map u zeta, hzeta])) := by
  let h := characterHomeomorph S u hforward hbackward
  letI : (Measure.map h.symm
      (CommutativeStateSpectralMeasure.stateSpectralMeasure
        (P.vectorState zeta hzeta))).Regular :=
    Measure.Regular.map h.symm
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  change
    ∫ chi, f chi ∂Measure.map h.symm
        (CommutativeStateSpectralMeasure.stateSpectralMeasure
          (P.vectorState zeta hzeta)) = _
  rw [h.symm.measurableEmbedding.integral_map]
  change
    ∫ chi, pullbackRealFunction P h.symm f chi
        ∂CommutativeStateSpectralMeasure.stateSpectralMeasure
          (P.vectorState zeta hzeta) = _
  rw [CommutativeStateSpectralMeasure.integral_stateSpectralMeasure,
    CommutativeStateSpectralMeasure.integral_stateSpectralMeasure,
    spectralLift_pullback_characterHomeomorph_symm P u hforward hbackward]
  change
    (⟪zeta,
      P.inclusionRep.hom
        ((restrictConjStarAlgEquiv S u hforward hbackward).symm
          (CommutativeStateSpectralMeasure.spectralLift f)) zeta⟫_ℂ).re =
    (⟪(u : H →L[ℂ] H) zeta,
      P.inclusionRep.hom
        (CommutativeStateSpectralMeasure.spectralLift f)
          ((u : H →L[ℂ] H) zeta)⟫_ℂ).re
  change
    (⟪zeta,
      (((restrictConjStarAlgEquiv S u hforward hbackward).symm
        (CommutativeStateSpectralMeasure.spectralLift f) : S) :
          H →L[ℂ] H) zeta⟫_ℂ).re = _
  rw [restrictConjStarAlgEquiv_symm_coe,
    Unitary.conjStarAlgAut_symm_apply]
  change
    (⟪zeta, (star (u : H →L[ℂ] H))
      (((CommutativeStateSpectralMeasure.spectralLift f : S) :
        H →L[ℂ] H) ((u : H →L[ℂ] H) zeta))⟫_ℂ).re = _
  rw [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

/-- **Measurable spectral quasi-invariance under a normalizing unitary.**
If the unitary and its inverse preserve the represented root-plane algebra
and move the unit vector by at most `epsilon`, then its scalar RMK spectral
measure obeys Kassabov's quadratic setwise estimate. -/
theorem measurableQuasiInvariantAtScale_characterHomeomorph
    (zeta : H) (hzeta : ‖zeta‖ = 1)
    (u : unitary (H →L[ℂ] H))
    (hforward : ∀ x : S,
      Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u x.1 ∈ S)
    (hbackward : ∀ x : S,
      (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u).symm x.1 ∈ S)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hmove : ‖(u : H →L[ℂ] H) zeta - zeta‖ ≤ epsilon) :
    MeasurableQuasiInvariantAtScale
      (CommutativeStateSpectralMeasure.stateSpectralMeasure
        (P.vectorState zeta hzeta)) epsilon
      (characterHomeomorph S u hforward hbackward) := by
  intro B hB _himage
  let h := characterHomeomorph S u hforward hbackward
  let uzeta : H := (u : H →L[ℂ] H) zeta
  have huzeta : ‖uzeta‖ = 1 := by
    change ‖(u : H →L[ℂ] H) zeta‖ = 1
    rw [Unitary.norm_map u zeta, hzeta]
  have hmap := map_characterHomeomorph_symm_stateSpectralMeasure
    P zeta hzeta u hforward hbackward
  have himageMass :
      (CommutativeStateSpectralMeasure.stateSpectralMeasure
        (P.vectorState zeta hzeta)).real (h '' B) =
      (CommutativeStateSpectralMeasure.stateSpectralMeasure
        (P.vectorState uzeta huzeta)).real B := by
    have happly := congrArg (fun mu : Measure X ↦ mu.real B) hmap
    have hset :
        Measure.map h.symm
            (CommutativeStateSpectralMeasure.stateSpectralMeasure
              (P.vectorState zeta hzeta)) B =
          CommutativeStateSpectralMeasure.stateSpectralMeasure
              (P.vectorState zeta hzeta) (h '' B) := by
      rw [h.symm.measurableEmbedding.map_apply, h.preimage_symm]
    have hsetReal :
        (Measure.map h.symm
          (CommutativeStateSpectralMeasure.stateSpectralMeasure
            (P.vectorState zeta hzeta))).real B =
        (CommutativeStateSpectralMeasure.stateSpectralMeasure
          (P.vectorState zeta hzeta)).real (h '' B) := by
      simpa only [measureReal_def] using congrArg ENNReal.toReal hset
    rw [hsetReal] at happly
    simpa [h, uzeta] using happly
  rw [himageMass]
  exact abs_measureReal_stateSpectralMeasure_sub_le
    P.inclusionRep zeta uzeta hzeta huzeta hepsilon hmove B hB

end Plane

end RepresentedRootPlaneSpectralQuasiInvariant

end GroupApproximation
