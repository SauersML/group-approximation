import GroupApproximation.Analysis.CStarContinuousMapNuclear
import GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeAverage.Rational
import Mathlib.Analysis.Complex.Order
import Mathlib.Topology.ContinuousMap.Ordered
import GroupApproximation.Meta.AxiomGuard

/-!
# States on `C(X)` are approximated by rational averages of point evaluations (lane nm-tww-01)

`X` is a compact Hausdorff space, and `τ : C(X, ℂ) →L[ℂ] ℂ` is positive and unital:
`0 ≤ f` implies that `τ f` is real and nonnegative, and `τ 1 = 1`. For every finite
`F ⊆ C(X, ℂ)` and every `ε > 0` there are `N > 0` and points `x : Fin N → X` with
`‖τ f - N⁻¹ ∑ i, f (x i)‖ ≤ ε` for all `f ∈ F`.

There is no Riesz–Markov step. Route:
* Put `δ = ε / 2 / (‖τ‖ + 1)`. The corpus partition of unity
  `CStarContinuousMapFiniteInterpolation.exists_variation_partition` (with `B = ℂ`) gives sample
  points `sample i` and weights `w i ≥ 0` with `∑ w i = 1` and `tsupport (w i)` inside the
  common `δ`-variation neighbourhood of `sample i`. The corpus lemma
  `norm_interpolation_evaluation_sub_le` then gives `‖∑ i, f (sample i) • w i - f‖ ≤ δ`
  for `f ∈ F`.
* The weights `t i = re τ (w i)` are nonnegative, `τ (w i) = t i` by positivity, and
  `∑ t i = 1` because `∑ w i = 1` and `τ 1 = 1`. Hence
  `‖τ f - ∑ t i f (sample i)‖ ≤ ‖τ‖ δ ≤ ε / 2`.
* `Rational.exists_average_approx`, with bound `B = ∑_{g ∈ F} ‖g‖`, replaces the convex
  combination by a rational average with error `≤ ε / 2`.
* Nonemptiness of `X` (needed by the corpus partition lemma) follows from `τ 1 = 1`: on an
  empty space `1 = 0` in `C(X, ℂ)`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace CommutativeAverage

open scoped ComplexOrder

noncomputable section

/-- A real continuous function regarded as a complex one. -/
def complexWeight {X : Type*} [TopologicalSpace X] (w : C(X, ℝ)) : C(X, ℂ) where
  toFun y := (w y : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp w.continuous

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeAverage.complexWeight

@[simp] theorem complexWeight_apply {X : Type*} [TopologicalSpace X] (w : C(X, ℝ)) (y : X) :
    complexWeight w y = (w y : ℂ) := rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeAverage.complexWeight_apply

theorem sum_complexWeight {X : Type*} [TopologicalSpace X] {k : ℕ} (w : Fin k → C(X, ℝ))
    (hwsum : ∀ y, ∑ i, w i y = 1) :
    ∑ i, complexWeight (w i) = 1 := by
  ext y
  rw [ContinuousMap.sum_apply, ContinuousMap.one_apply]
  simp only [complexWeight_apply]
  rw [← Complex.ofReal_sum, hwsum y, Complex.ofReal_one]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeAverage.sum_complexWeight

/-- The corpus interpolation of finitely many point values, at `B = ℂ`, is the explicit
weighted sum `∑ i, f (sample i) • w i`. -/
theorem interpolation_eq_sum {X : Type*} [TopologicalSpace X] [CompactSpace X] {k : ℕ}
    (w : Fin k → C(X, ℝ)) (hw : ∀ i y, 0 ≤ w i y) (sample : Fin k → X) (f : C(X, ℂ)) :
    CStarContinuousMapFiniteInterpolation.finiteInterpolation (B := ℂ) w
        (CStarContinuousMapFiniteInterpolation.finiteEvaluationStarAlgHom sample f) =
      ∑ i, f (sample i) • complexWeight (w i) := by
  ext y
  rw [CStarContinuousMapFiniteInterpolation.finiteInterpolation_apply w hw,
    ContinuousMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [CStarContinuousMapFiniteInterpolation.finiteEvaluationStarAlgHom_apply,
    ContinuousMap.smul_apply, complexWeight_apply, smul_eq_mul]
  ring

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeAverage.interpolation_eq_sum

/-- **Lane nm-tww-01.** A positive unital functional on `C(X, ℂ)`, with `X` compact
Hausdorff, is approximated on any finite set, to any precision, by a rational average of
point evaluations. -/
theorem exists_pointEvaluation_average (X : Type*) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (τ : C(X, ℂ) →L[ℂ] ℂ)
    (hpos : ∀ f : C(X, ℂ), 0 ≤ f → 0 ≤ (τ f).re ∧ (τ f).im = 0) (hunit : τ 1 = 1)
    (F : Finset C(X, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (_ : 0 < N) (x : Fin N → X), ∀ f ∈ F,
      ‖τ f - (N : ℂ)⁻¹ * ∑ i, f (x i)‖ ≤ ε := by
  have hne : Nonempty X := by
    by_contra hX
    have h10 : (1 : C(X, ℂ)) = 0 := ContinuousMap.ext fun y => (hX ⟨y⟩).elim
    have h := hunit
    rw [h10, map_zero] at h
    exact zero_ne_one h
  have hτ1 : 0 < ‖τ‖ + 1 := add_pos_of_nonneg_of_pos (norm_nonneg τ) one_pos
  have hδ : 0 < ε / 2 / (‖τ‖ + 1) := div_pos (half_pos hε) hτ1
  obtain ⟨k, sample, w, hwsub, hwsum, hw⟩ :=
    CStarContinuousMapFiniteInterpolation.exists_variation_partition (B := ℂ) F hδ
  have hwposC : ∀ i, (0 : C(X, ℂ)) ≤ complexWeight (w i) := fun i =>
    ContinuousMap.le_def.2 fun y => by
      rw [ContinuousMap.zero_apply, complexWeight_apply]
      exact Complex.zero_le_real.2 (hw i y)
  have hτw : ∀ i, τ (complexWeight (w i)) = ((τ (complexWeight (w i))).re : ℂ) := fun i =>
    Complex.ext (by rw [Complex.ofReal_re])
      (by rw [Complex.ofReal_im]; exact (hpos _ (hwposC i)).2)
  have ht0 : ∀ i, 0 ≤ (τ (complexWeight (w i))).re := fun i => (hpos _ (hwposC i)).1
  have ht1 : ∑ i, (τ (complexWeight (w i))).re = 1 := by
    have h1 : τ (∑ i, complexWeight (w i)) = 1 := by
      rw [sum_complexWeight w hwsum, hunit]
    rw [map_sum] at h1
    have h2 := congrArg Complex.re h1
    rwa [Complex.re_sum, Complex.one_re] at h2
  obtain ⟨N, hN, x, hx⟩ := exists_average_approx sample
    (fun i => (τ (complexWeight (w i))).re) ht0 ht1 (∑ g ∈ F, ‖g‖) (half_pos hε)
  refine ⟨N, hN, x, fun f hf => ?_⟩
  have hbound : ∀ i, ‖f (sample i)‖ ≤ ∑ g ∈ F, ‖g‖ := fun i =>
    (ContinuousMap.norm_coe_le_norm f (sample i)).trans
      (Finset.single_le_sum (fun g _ => norm_nonneg g) hf)
  have happrox := hx f hbound
  have hinterp := CStarContinuousMapFiniteInterpolation.norm_interpolation_evaluation_sub_le
    (B := ℂ) F hδ sample w hwsub hwsum hw f hf
  rw [interpolation_eq_sum w hw sample f] at hinterp
  have hτg : τ (∑ i, f (sample i) • complexWeight (w i)) =
      ∑ i, ((τ (complexWeight (w i))).re : ℂ) * f (sample i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, ← hτw i, mul_comm]
  have hfirst : ‖τ f - ∑ i, ((τ (complexWeight (w i))).re : ℂ) * f (sample i)‖ ≤ ε / 2 := by
    rw [← hτg, ← map_sub]
    calc
      ‖τ (f - ∑ i, f (sample i) • complexWeight (w i))‖
          ≤ ‖τ‖ * ‖f - ∑ i, f (sample i) • complexWeight (w i)‖ := τ.le_opNorm _
      _ ≤ ‖τ‖ * (ε / 2 / (‖τ‖ + 1)) :=
        mul_le_mul_of_nonneg_left (by rw [norm_sub_rev]; exact hinterp) (norm_nonneg τ)
      _ ≤ (‖τ‖ + 1) * (ε / 2 / (‖τ‖ + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = ε / 2 := mul_div_cancel₀ (ε / 2) hτ1.ne'
  calc
    ‖τ f - (N : ℂ)⁻¹ * ∑ i, f (x i)‖
        = ‖(τ f - ∑ i, ((τ (complexWeight (w i))).re : ℂ) * f (sample i)) +
            (∑ i, ((τ (complexWeight (w i))).re : ℂ) * f (sample i) -
              (N : ℂ)⁻¹ * ∑ i, f (x i))‖ := by
      rw [sub_add_sub_cancel]
    _ ≤ ‖τ f - ∑ i, ((τ (complexWeight (w i))).re : ℂ) * f (sample i)‖ +
          ‖∑ i, ((τ (complexWeight (w i))).re : ℂ) * f (sample i) -
            (N : ℂ)⁻¹ * ∑ i, f (x i)‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hfirst happrox
    _ = ε := add_halves ε

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeAverage.exists_pointEvaluation_average

end

end CommutativeAverage
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
