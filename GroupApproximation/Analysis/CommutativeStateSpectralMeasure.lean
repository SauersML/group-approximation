import GroupApproximation.Analysis.CStarStateGNS
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Spectral measures of states on commutative C-star algebras

This file constructs the scalar spectral measure needed for the integral
root-plane argument.  If `A` is a commutative unital C-star algebra and
`phi` is a state on `A`, Gelfand duality transports the real part of `phi`
to a positive real-linear functional on the continuous real-valued functions
on `characterSpace ℂ A`.  Real Riesz--Markov--Kakutani then gives an honest
finite regular Borel measure on that compact space.

For every `a : A`, the measure integrates the squared character displacement
`|chi(a) - 1|^2` to the state value of
`star (a - 1) * (a - 1)`.  This is the scalar spectral-measure identity.  It
uses only Gelfand duality, positivity of states, and RMK; no spectral theorem,
literature premise, or finite-dimensional approximation is assumed.
-/

namespace GroupApproximation

namespace CommutativeStateSpectralMeasure

open CStarState WeakDual MeasureTheory

universe u

variable {A : Type u} [CommCStarAlgebra A]

local notation "Χ" => characterSpace ℂ A

noncomputable local instance : MeasurableSpace Χ := borel Χ
local instance : BorelSpace Χ := ⟨rfl⟩

/-! ### Transporting real functions through Gelfand duality -/

/-- A state cannot exist on the trivial unital algebra: its underlying linear
map sends zero to zero, whereas unitality sends one to one. -/
private theorem state_nontrivial (phi : State A) : Nontrivial A := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  have hone := phi.map_one
  rw [h, map_zero] at hone
  exact zero_ne_one hone

/-- Regard a real compactly supported continuous function on the compact
character space as a complex continuous function. -/
noncomputable def complexifyRealFunction
    (f : CompactlySupportedContinuousMap Χ ℝ) : C(Χ, ℂ) where
  toFun χ := (f χ : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp f.continuous_toFun

@[simp] theorem complexifyRealFunction_apply
    (f : CompactlySupportedContinuousMap Χ ℝ) (χ : Χ) :
    complexifyRealFunction f χ = (f χ : ℂ) := rfl

/-- The element of `A` corresponding under Gelfand duality to a real
continuous function on its character space. -/
noncomputable def spectralLift
    (f : CompactlySupportedContinuousMap Χ ℝ) : A :=
  (gelfandStarTransform A).symm (complexifyRealFunction f)

theorem spectralLift_add
    (f g : CompactlySupportedContinuousMap Χ ℝ) :
    spectralLift (f + g) = spectralLift f + spectralLift g := by
  have hfun : complexifyRealFunction (f + g) =
      complexifyRealFunction f + complexifyRealFunction g := by
    ext χ
    simp [complexifyRealFunction]
  unfold spectralLift
  rw [hfun, map_add]

theorem spectralLift_smul (r : ℝ)
    (f : CompactlySupportedContinuousMap Χ ℝ) :
    spectralLift (r • f) = (r : ℂ) • spectralLift f := by
  have hfun : complexifyRealFunction (r • f) =
      (r : ℂ) • complexifyRealFunction f := by
    ext χ
    simp [complexifyRealFunction]
  unfold spectralLift
  rw [hfun, map_smul]

theorem spectralLift_sub
    (f g : CompactlySupportedContinuousMap Χ ℝ) :
    spectralLift (f - g) = spectralLift f - spectralLift g := by
  have hfun : complexifyRealFunction (f - g) =
      complexifyRealFunction f - complexifyRealFunction g := by
    ext χ
    simp [complexifyRealFunction]
  unfold spectralLift
  rw [hfun, map_sub]

/-- Positivity survives the inverse Gelfand transform.  The proof is
concrete: a nonnegative real function is the square of its continuous square
root, so its lift is literally `star b * b`. -/
theorem state_spectralLift_nonneg (phi : State A)
    (f : CompactlySupportedContinuousMap Χ ℝ) (hf : 0 ≤ f) :
    0 ≤ (phi.toCLM (spectralLift f)).re := by
  letI := state_nontrivial phi
  let q : C(Χ, ℂ) :=
    { toFun := fun χ => (Real.sqrt (f χ) : ℂ)
      continuous_toFun := Complex.continuous_ofReal.comp
        (Real.continuous_sqrt.comp f.continuous_toFun) }
  let b : A := (gelfandStarTransform A).symm q
  have hfun : complexifyRealFunction f = star q * q := by
    ext χ
    have hfχ : 0 ≤ f χ :=
      (CompactlySupportedContinuousMap.le_def.mp hf) χ
    have hsqrt : Real.sqrt (f χ) * Real.sqrt (f χ) = f χ := by
      simpa [pow_two] using Real.sq_sqrt hfχ
    change (f χ : ℂ) =
      star (Real.sqrt (f χ) : ℂ) * (Real.sqrt (f χ) : ℂ)
    simpa [Complex.star_def] using
      congrArg (fun x : ℝ => (x : ℂ)) hsqrt.symm
  have hsq : spectralLift f = star b * b := by
    unfold spectralLift
    rw [hfun, map_mul, map_star]
  rw [hsq]
  exact (phi.star_mul_self_nonneg b).1

/-! ### The RMK functional and measure -/

/-- The real positive functional obtained from a state by inverse Gelfand
transform. -/
noncomputable def stateRieszFunctional (phi : State A) :
    CompactlySupportedContinuousMap Χ ℝ →ₚ[ℝ] ℝ where
  toFun f := (phi.toCLM (spectralLift f)).re
  map_add' f g := by
    rw [spectralLift_add, map_add, Complex.add_re]
  map_smul' r f := by
    rw [spectralLift_smul, map_smul]
    simp
  monotone' := by
    intro f g hfg
    have hnonneg : 0 ≤ (phi.toCLM (spectralLift (g - f))).re :=
      state_spectralLift_nonneg phi (g - f) (sub_nonneg.mpr hfg)
    rw [spectralLift_sub, map_sub, Complex.sub_re] at hnonneg
    exact sub_nonneg.mp hnonneg

@[simp] theorem stateRieszFunctional_apply (phi : State A)
    (f : CompactlySupportedContinuousMap Χ ℝ) :
    stateRieszFunctional phi f = (phi.toCLM (spectralLift f)).re := rfl

/-- The finite regular Borel measure representing the state on the character
space. -/
noncomputable def stateSpectralMeasure (phi : State A) : Measure Χ :=
  RealRMK.rieszMeasure (stateRieszFunctional phi)

noncomputable instance stateSpectralMeasure_isFinite (phi : State A) :
    IsFiniteMeasure (stateSpectralMeasure phi) := by
  unfold stateSpectralMeasure
  infer_instance

noncomputable instance stateSpectralMeasure_regular (phi : State A) :
    (stateSpectralMeasure phi).Regular := by
  unfold stateSpectralMeasure
  infer_instance

/-- RMK representation for every real continuous test function. -/
theorem integral_stateSpectralMeasure (phi : State A)
    (f : CompactlySupportedContinuousMap Χ ℝ) :
    ∫ χ, f χ ∂stateSpectralMeasure phi =
      (phi.toCLM (spectralLift f)).re := by
  exact RealRMK.integral_rieszMeasure (stateRieszFunctional phi) f

/-! ### The scalar displacement identity -/

/-- The real part of the Gelfand transform, packaged as a compactly supported
continuous real function. -/
noncomputable def gelfandRealPart (a : A) :
    CompactlySupportedContinuousMap Χ ℝ :=
  CompactlySupportedContinuousMap.continuousMapEquiv
    { toFun := fun χ => (χ a).re
      continuous_toFun := Complex.continuous_re.comp
        ((gelfandStarTransform A) a).continuous_toFun }

@[simp] theorem gelfandRealPart_apply (a : A) (χ : Χ) :
    gelfandRealPart a χ = (χ a).re := by
  simp [gelfandRealPart]

/-- For a self-adjoint element, lifting the real part of its Gelfand
transform returns the element itself. -/
theorem spectralLift_gelfandRealPart (a : A) (ha : IsSelfAdjoint a) :
    spectralLift (gelfandRealPart a) = a := by
  have hfun : complexifyRealFunction (gelfandRealPart a) =
      (gelfandStarTransform A) a := by
    ext χ
    have hc : star (χ a) = χ a := by
      calc
        star (χ a) = χ (star a) := by
          simpa using congrArg (fun f : C(Χ, ℂ) => f χ)
            (map_star (gelfandStarTransform A) a).symm
        _ = χ a := by rw [ha.star_eq]
    have him : (χ a).im = 0 := Complex.conj_eq_iff_im.mp hc
    apply Complex.ext
    · simp [complexifyRealFunction, gelfandRealPart]
    · simp [complexifyRealFunction, gelfandRealPart, him]
  unfold spectralLift
  rw [hfun]
  exact (gelfandStarTransform A).symm_apply_apply a

/-- The representing measure integrates the real Gelfand transform of a
self-adjoint element to its state value. -/
theorem integral_gelfandRealPart (phi : State A) (a : A)
    (ha : IsSelfAdjoint a) :
    ∫ χ, gelfandRealPart a χ ∂stateSpectralMeasure phi =
      (phi.toCLM a).re := by
  rw [integral_stateSpectralMeasure,
    spectralLift_gelfandRealPart a ha]

/-- The squared scalar displacement observed by each character. -/
noncomputable def characterDisplacementSq (a : A) :
    CompactlySupportedContinuousMap Χ ℝ :=
  gelfandRealPart (star (a - 1) * (a - 1))

@[simp] theorem characterDisplacementSq_apply (a : A) (χ : Χ) :
    characterDisplacementSq a χ = ‖χ a - 1‖ ^ 2 := by
  have hstar : χ (star (a - 1)) = star (χ a - 1) := by
    rw [map_star, map_sub, map_one]
  rw [characterDisplacementSq, gelfandRealPart_apply, map_mul, hstar,
    map_sub, map_one, Complex.star_def]
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

/-- **Scalar spectral-measure displacement identity.**  Squared character
displacement integrates exactly to the state value of the positive square
`star (a - 1) * (a - 1)`. -/
theorem integral_characterDisplacementSq (phi : State A) (a : A) :
    ∫ χ, characterDisplacementSq a χ ∂stateSpectralMeasure phi =
      (phi.toCLM (star (a - 1) * (a - 1))).re := by
  exact integral_gelfandRealPart phi (star (a - 1) * (a - 1))
    (IsSelfAdjoint.star_mul_self (a - 1))

end CommutativeStateSpectralMeasure

end GroupApproximation
