import GroupApproximation.Analysis.CuntzPedersenJordanTracial

/-!
# Model tests for the Jordan-decomposition hypotheses

Repository standing order: every hypothesis-bearing `Prop` is checked against
a concrete instance before it is used.  `CuntzPedersenJordanTracial` introduces
two of them, `HasJordanDecomposition` and `HasUniqueJordanDecomposition`, and
consumes a third, `HasCuntzPedersenSeparation`.  This file discharges all
three at `A = ℂ` **unconditionally**, which in particular shows that the two
Jordan hypotheses are jointly satisfiable and that the transfer theorem
`hasCuntzPedersenSeparation_of_jordan` produces the right conclusion there.

The test at `ℂ` is a real test of the *analytic* content (positivity,
norm-additivity, minimality) but not of the *tracial* content, since every
functional on a commutative algebra is tracial.  The tracial machinery is
therefore separately round-tripped at an arbitrary unital C-star-algebra:
`normalizedTracialState_tracialStateCLM` shows that the positive/tracial
predicates and the normalization recover an arbitrary bundled `TracialState`
on the nose.
-/

namespace GroupApproximation
namespace CuntzPedersenJordanModelTest

open CuntzPedersenCoronaObstruction CuntzPedersenTraceZero
  CuntzPedersenJordanTracial
open scoped ComplexOrder

noncomputable section

set_option linter.unusedSectionVars false

/-! ## Round trip at an arbitrary unital C-star-algebra -/

section General

variable {A : Type*} [CStarAlgebra A]

theorem isPositiveFunctional_tracialStateCLM (τ : TracialState A) :
    IsPositiveFunctional (HNNTrace.tracialStateCLM τ) := by
  intro z
  rw [HNNTrace.tracialStateCLM_apply]
  exact τ.map_star_mul_self_nonneg z

theorem isTracialFunctional_tracialStateCLM (τ : TracialState A) :
    IsTracialFunctional (HNNTrace.tracialStateCLM τ) := by
  intro a b
  rw [HNNTrace.tracialStateCLM_apply, HNNTrace.tracialStateCLM_apply]
  exact τ.map_mul_comm a b

theorem tracialStateCLM_one_ne_zero (τ : TracialState A) :
    HNNTrace.tracialStateCLM τ 1 ≠ 0 := by
  rw [HNNTrace.tracialStateCLM_apply, τ.apply_one]
  exact one_ne_zero

/-- Normalizing the positive tracial functional attached to a tracial state
returns that state.  This is the round trip which certifies that
`IsPositiveFunctional`, `IsTracialFunctional` and `normalizedTracialState`
name the intended notions, and it holds at an arbitrary, possibly
noncommutative, unital C-star-algebra. -/
theorem normalizedTracialState_tracialStateCLM (τ : TracialState A) (a : A) :
    normalizedTracialState (isPositiveFunctional_tracialStateCLM τ)
      (isTracialFunctional_tracialStateCLM τ)
      (tracialStateCLM_one_ne_zero τ) a = τ a := by
  rw [normalizedTracialState_apply, HNNTrace.tracialStateCLM_apply,
    HNNTrace.tracialStateCLM_apply, τ.apply_one, inv_one, one_mul]

end General

/-! ## Bounded functionals on `ℂ` -/

/-- Every bounded functional on `ℂ` is multiplication by its value at `1`. -/
theorem apply_eq_mul (f : ℂ →L[ℂ] ℂ) (z : ℂ) : f z = z * f 1 := by
  have h : f (z • (1 : ℂ)) = z • f 1 := map_smul f z 1
  rwa [smul_eq_mul, mul_one, smul_eq_mul] at h

theorem ext_of_apply_one {f g : ℂ →L[ℂ] ℂ} (h : f 1 = g 1) : f = g :=
  ContinuousLinearMap.ext fun z ↦ by rw [apply_eq_mul f z, apply_eq_mul g z, h]

theorem norm_eq_norm_apply_one (f : ℂ →L[ℂ] ℂ) : ‖f‖ = ‖f 1‖ := by
  refine le_antisymm (f.opNorm_le_bound (norm_nonneg _) fun z ↦ ?_) ?_
  · calc ‖f z‖ = ‖z‖ * ‖f 1‖ := by rw [apply_eq_mul f z, norm_mul]
      _ = ‖f 1‖ * ‖z‖ := mul_comm _ _
  · simpa using f.le_opNorm 1

/-- Multiplication by a scalar, as a bounded functional on `ℂ`. -/
def mulCLM (c : ℂ) : ℂ →L[ℂ] ℂ := c • ContinuousLinearMap.id ℂ ℂ

@[simp] theorem mulCLM_apply (c z : ℂ) : mulCLM c z = c * z := rfl

@[simp] theorem mulCLM_one (c : ℂ) : mulCLM c 1 = c := by
  rw [mulCLM_apply, mul_one]

theorem norm_mulCLM (c : ℂ) : ‖mulCLM c‖ = ‖c‖ := by
  rw [norm_eq_norm_apply_one, mulCLM_one]

/-- On `ℂ`, positivity of a bounded functional is nonnegativity at `1`. -/
theorem isPositiveFunctional_iff (f : ℂ →L[ℂ] ℂ) :
    IsPositiveFunctional f ↔ 0 ≤ f 1 := by
  constructor
  · intro hf
    exact hf.apply_one_nonneg
  · intro h z
    rw [apply_eq_mul f (star z * z)]
    exact mul_nonneg_complex (star_mul_self_nonneg z) h

/-- On `ℂ`, every bounded functional is tracial. -/
theorem isTracialFunctional_complex (f : ℂ →L[ℂ] ℂ) : IsTracialFunctional f :=
  fun a b ↦ by rw [mul_comm]

/-- A positive bounded functional on `ℂ` is multiplication by a nonnegative
real, whose value is its norm. -/
theorem positive_scalar {p : ℂ →L[ℂ] ℂ} (hp : IsPositiveFunctional p) :
    ∃ a : ℝ, 0 ≤ a ∧ p 1 = ((a : ℝ) : ℂ) ∧ ‖p‖ = a := by
  have h := hp.apply_one_nonneg
  obtain ⟨a, ha0, hpa⟩ : ∃ a : ℝ, 0 ≤ a ∧ p 1 = ((a : ℝ) : ℂ) :=
    ⟨(p 1).re, (Complex.nonneg_iff.mp h).1, eq_ofReal_re_of_nonneg h⟩
  refine ⟨a, ha0, hpa, ?_⟩
  rw [norm_eq_norm_apply_one, hpa, Complex.norm_of_nonneg ha0]

/-! ## The two Jordan hypotheses hold at `ℂ` -/

theorem hasJordanDecomposition_complex : HasJordanDecomposition ℂ := by
  intro f hf
  have hstar : f 1 = star (f 1) := by
    have h := hf 1
    rwa [star_one] at h
  have him : (f 1).im = 0 := by
    have h := congrArg Complex.im hstar
    rw [Complex.star_def, Complex.conj_im] at h
    linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, f 1 = ((r : ℝ) : ℂ) := by
    refine ⟨(f 1).re, ?_⟩
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im]
      exact him
  obtain ⟨a, b, ha, hb, hab, habs⟩ :
      ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a - b = r ∧ a + b = |r| := by
    rcases le_total 0 r with h | h
    · refine ⟨r, 0, h, le_rfl, by ring, ?_⟩
      rw [abs_of_nonneg h]
      ring
    · refine ⟨0, -r, le_rfl, by linarith, by ring, ?_⟩
      rw [← abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ -r)]
      ring
  refine ⟨mulCLM ((a : ℝ) : ℂ), mulCLM ((b : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · rw [isPositiveFunctional_iff, mulCLM_one]
    exact Complex.zero_le_real.mpr ha
  · rw [isPositiveFunctional_iff, mulCLM_one]
    exact Complex.zero_le_real.mpr hb
  · refine ext_of_apply_one ?_
    rw [hr]
    show ((r : ℝ) : ℂ) = mulCLM ((a : ℝ) : ℂ) 1 - mulCLM ((b : ℝ) : ℂ) 1
    rw [mulCLM_one, mulCLM_one, ← Complex.ofReal_sub, hab]
  · rw [norm_eq_norm_apply_one f, hr, norm_mulCLM, norm_mulCLM,
      Complex.norm_of_nonneg ha, Complex.norm_of_nonneg hb, Complex.norm_real,
      Real.norm_eq_abs, habs]

theorem hasUniqueJordanDecomposition_complex :
    HasUniqueJordanDecomposition ℂ := by
  intro p q p' q' hp hq hp' hq' hsub hn hn'
  obtain ⟨a, ha, hpa, hna⟩ := positive_scalar hp
  obtain ⟨b, hb, hqb, hnb⟩ := positive_scalar hq
  obtain ⟨a', ha', hpa', hna'⟩ := positive_scalar hp'
  obtain ⟨b', hb', hqb', hnb'⟩ := positive_scalar hq'
  have hval : p 1 - q 1 = p' 1 - q' 1 := DFunLike.congr_fun hsub 1
  have hdiff : a - b = a' - b' := by
    have h : ((a - b : ℝ) : ℂ) = ((a' - b' : ℝ) : ℂ) := by
      rw [Complex.ofReal_sub, Complex.ofReal_sub, ← hpa, ← hqb, ← hpa', ← hqb']
      exact hval
    exact_mod_cast h
  have hnormsub : ‖p - q‖ = |a - b| := by
    have hpq1 : (p - q) 1 = p 1 - q 1 := rfl
    have h1 : (p - q) 1 = ((a - b : ℝ) : ℂ) := by
      rw [hpq1, hpa, hqb, Complex.ofReal_sub]
    rw [norm_eq_norm_apply_one (p - q), h1, Complex.norm_real, Real.norm_eq_abs]
  have hnormsub' : ‖p' - q'‖ = |a' - b'| := by
    have hpq1 : (p' - q') 1 = p' 1 - q' 1 := rfl
    have h1 : (p' - q') 1 = ((a' - b' : ℝ) : ℂ) := by
      rw [hpq1, hpa', hqb', Complex.ofReal_sub]
    rw [norm_eq_norm_apply_one (p' - q'), h1, Complex.norm_real,
      Real.norm_eq_abs]
  have hkey : |a - b| = a + b := by
    rw [← hnormsub, hn, hna, hnb]
  have hkey' : |a' - b'| = a' + b' := by
    rw [← hnormsub', hn', hna', hnb']
  have hprod : a * b = 0 := by
    have hsq : (a - b) ^ 2 = (a + b) ^ 2 := by
      rw [← sq_abs (a - b), hkey]
    linear_combination (-1 / 4 : ℝ) * hsq
  have hprod' : a' * b' = 0 := by
    have hsq : (a' - b') ^ 2 = (a' + b') ^ 2 := by
      rw [← sq_abs (a' - b'), hkey']
    linear_combination (-1 / 4 : ℝ) * hsq
  have hsplit := mul_eq_zero.mp hprod
  have hsplit' := mul_eq_zero.mp hprod'
  have hfinal : a = a' ∧ b = b' := by
    rcases hsplit with h | h <;> rcases hsplit' with h' | h' <;>
      exact ⟨by linarith, by linarith⟩
  refine ⟨ext_of_apply_one ?_, ext_of_apply_one ?_⟩
  · rw [hpa, hpa', hfinal.1]
  · rw [hqb, hqb', hfinal.2]

/-! ## Cuntz--Pedersen separation at `ℂ`, proved twice -/

/-- The canonical tracial state of `ℂ`. -/
def complexTracialState : TracialState ℂ where
  toLinearMap := LinearMap.id
  map_one := rfl
  map_star_mul_self_nonneg x := star_mul_self_nonneg x
  map_mul_comm x y := mul_comm x y

@[simp] theorem complexTracialState_apply (z : ℂ) : complexTracialState z = z :=
  rfl

/-- Additive self-commutators vanish on a commutative algebra, so the
Cuntz--Pedersen trace-zero space of `ℂ` is the origin. -/
theorem traceZeroSpace_complex : traceZeroSpace ℂ = {0} := by
  have hsets : {x : ℂ | IsFiniteSelfCommutatorSum x} = {0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨ell, z, rfl⟩
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [selfCommutator_apply, mul_comm, sub_self]
    · rintro rfl
      exact isFiniteSelfCommutatorSum_zero
  show closure {x : ℂ | IsFiniteSelfCommutatorSum x} = {0}
  rw [hsets, closure_singleton]

/-- Direct proof of the separation property at `ℂ`. -/
theorem hasCuntzPedersenSeparation_complex : HasCuntzPedersenSeparation ℂ := by
  intro x _ hx
  rw [traceZeroSpace_complex] at hx
  refine ⟨complexTracialState, fun hτ ↦ hx ?_⟩
  exact Set.mem_singleton_iff.mpr hτ

/-- The same property obtained through the transfer theorem.  This is the
model test proper: the Jordan hypotheses are satisfiable, and running them
through `hasCuntzPedersenSeparation_of_jordan` yields exactly the property
established directly above. -/
theorem hasCuntzPedersenSeparation_complex_via_jordan :
    HasCuntzPedersenSeparation ℂ :=
  hasCuntzPedersenSeparation_of_jordan hasJordanDecomposition_complex
    hasUniqueJordanDecomposition_complex

end

end CuntzPedersenJordanModelTest
end GroupApproximation
