import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Topology.MetricSpace.HausdorffDistance
import GroupApproximation.Meta.AxiomGuard

/-!
# The distance to the invertible elements of a unital C⋆-algebra

`distGL x = dist(x, GL(A))`.  Stable rank one is density of `GL(A)`, i.e. `distGL = 0`
everywhere (`dense_invertibles_iff`).  What the Dykema–Haagerup–Rørdam argument uses:

* `distGL_le_spectralRadius` — `dist(x, GL(A)) ≤ r(x)`: for `|λ| > r(x)` the element
  `x − λ` is invertible and at distance `|λ|` from `x` (DHR, the display before their
  (3.3));
* `distGL_mul_of_mem_unitary` — left multiplication by a unitary is an isometry that
  preserves `GL(A)`, so it preserves `dist(·, GL(A))` (DHR (3.3));
* `nonneg_mul_mem_closure_invertibles` — `c·s` with `c ≥ 0` and `s` invertible is a
  limit of the invertibles `(c + ε)·s` (Farah–Rørdam, proof of Proposition 3);
* `distGL_le_norm` — `dist(x, GL(A)) ≤ ‖x‖`.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` (stable rank one of `C*_r(Q)`).
Certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace DistanceToInvertibles

/-- The invertible elements of a monoid, as a set. -/
def invertibles (M : Type*) [Monoid M] : Set M := {y : M | IsUnit y}

@[simp] theorem mem_invertibles {M : Type*} [Monoid M] {y : M} :
    y ∈ invertibles M ↔ IsUnit y := Iff.rfl

theorem invertibles_nonempty (M : Type*) [Monoid M] : (invertibles M).Nonempty :=
  ⟨1, isUnit_one⟩

variable {A : Type*} [CStarAlgebra A]

/-- `dist(x, GL(A))`. -/
noncomputable def distGL (x : A) : ℝ := Metric.infDist x (invertibles A)

theorem distGL_nonneg (x : A) : 0 ≤ distGL x := Metric.infDist_nonneg

theorem distGL_le_norm_sub {x y : A} (hy : IsUnit y) : distGL x ≤ ‖x - y‖ := by
  rw [← dist_eq_norm]
  exact Metric.infDist_le_dist_of_mem (mem_invertibles.mpr hy)

theorem distGL_le_distGL_add_norm_sub (x y : A) : distGL x ≤ distGL y + ‖x - y‖ := by
  rw [← dist_eq_norm]
  exact Metric.infDist_le_infDist_add_dist

theorem exists_isUnit_norm_sub_lt {x : A} {r : ℝ} (h : distGL x < r) :
    ∃ z : A, IsUnit z ∧ ‖x - z‖ < r := by
  obtain ⟨z, hz, hd⟩ := (Metric.infDist_lt_iff (invertibles_nonempty A)).mp h
  exact ⟨z, hz, by rwa [← dist_eq_norm]⟩

theorem distGL_eq_zero_of_mem_closure {x : A} (hx : x ∈ closure (invertibles A)) :
    distGL x = 0 :=
  Metric.infDist_zero_of_mem_closure hx

theorem distGL_le_norm_sub_of_mem_closure {x y : A} (hy : y ∈ closure (invertibles A)) :
    distGL x ≤ ‖x - y‖ := by
  have h := distGL_le_distGL_add_norm_sub x y
  rwa [distGL_eq_zero_of_mem_closure hy, zero_add] at h

/-- **Stable rank one is `dist(·, GL(A)) = 0`.** -/
theorem dense_invertibles_iff : Dense (invertibles A) ↔ ∀ x : A, distGL x = 0 := by
  constructor
  · intro h x
    exact distGL_eq_zero_of_mem_closure (h x)
  · intro h x
    exact (Metric.mem_closure_iff_infDist_zero (invertibles_nonempty A)).mpr (h x)

/-- **`dist(x, GL(A)) ≤ r(x)`.** -/
theorem distGL_le_spectralRadius (x : A) : distGL x ≤ (spectralRadius ℂ x).toReal := by
  obtain hA | hA := subsingleton_or_nontrivial A
  · rw [distGL, Metric.infDist_zero_of_mem (mem_invertibles.mpr (isUnit_of_subsingleton x))]
    exact ENNReal.toReal_nonneg
  have hfin : spectralRadius ℂ x ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (spectrum.spectralRadius_le_nnnorm x)
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  have hr0 : 0 < r := lt_of_le_of_lt ENNReal.toReal_nonneg hr
  have hk : (r : ℂ) ∉ spectrum ℂ x := by
    intro hmem
    have h1 : ((‖(r : ℂ)‖₊ : NNReal) : ENNReal) ≤ spectralRadius ℂ x :=
      le_iSup₂ (α := ENNReal) (r : ℂ) hmem
    have h2 := ENNReal.toReal_mono hfin h1
    rw [ENNReal.coe_toReal, coe_nnnorm, Complex.norm_of_nonneg hr0.le] at h2
    linarith
  have hunit : IsUnit (x - algebraMap ℂ A (r : ℂ)) := by
    have h := spectrum.notMem_iff.mp hk
    rw [← neg_sub]
    exact h.neg
  calc distGL x ≤ ‖x - (x - algebraMap ℂ A (r : ℂ))‖ := distGL_le_norm_sub hunit
    _ = r := by rw [sub_sub_cancel, norm_algebraMap', Complex.norm_of_nonneg hr0.le]

/-- **`dist(x, GL(A)) ≤ ‖x‖`.** -/
theorem distGL_le_norm (x : A) : distGL x ≤ ‖x‖ := by
  obtain hA | hA := subsingleton_or_nontrivial A
  · rw [distGL, Metric.infDist_zero_of_mem (mem_invertibles.mpr (isUnit_of_subsingleton x))]
    exact norm_nonneg x
  refine (distGL_le_spectralRadius x).trans ?_
  have h := spectrum.spectralRadius_le_nnnorm (𝕜 := ℂ) x
  have h2 := ENNReal.toReal_mono ENNReal.coe_ne_top h
  rwa [ENNReal.coe_toReal, coe_nnnorm] at h2

theorem isUnit_of_mem_unitary {u : A} (hu : u ∈ unitary A) : IsUnit u := by
  obtain ⟨h1, h2⟩ := Unitary.mem_iff.mp hu
  exact ⟨⟨u, star u, h2, h1⟩, rfl⟩

theorem distGL_mul_le_of_mem_unitary {u : A} (hu : u ∈ unitary A) (x : A) :
    distGL (u * x) ≤ distGL x := by
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  obtain ⟨z, hz, hxz⟩ := exists_isUnit_norm_sub_lt hr
  calc distGL (u * x) ≤ ‖u * x - u * z‖ :=
        distGL_le_norm_sub ((isUnit_of_mem_unitary hu).mul hz)
    _ = ‖x - z‖ := by rw [← mul_sub, CStarRing.norm_mem_unitary_mul _ hu]
    _ ≤ r := hxz.le

/-- **Left multiplication by a unitary preserves `dist(·, GL(A))`.** -/
theorem distGL_mul_of_mem_unitary {u : A} (hu : u ∈ unitary A) (x : A) :
    distGL (u * x) = distGL x := by
  refine le_antisymm (distGL_mul_le_of_mem_unitary hu x) ?_
  have h := distGL_mul_le_of_mem_unitary (Unitary.star_mem hu) (u * x)
  rwa [← mul_assoc, (Unitary.mem_iff.mp hu).1, one_mul] at h

variable [PartialOrder A] [StarOrderedRing A] in
theorem isUnit_add_algebraMap_of_nonneg {c : A} (hc : 0 ≤ c) {η : ℝ} (hη : 0 < η) :
    IsUnit (c + algebraMap ℝ A η) := by
  rw [← spectrum.zero_notMem_iff ℝ, ← spectrum.add_singleton_eq]
  rintro ⟨t, ht, e, he, hte⟩
  rw [Set.mem_singleton_iff] at he
  have h0 : 0 ≤ t := spectrum_nonneg_of_nonneg hc ht
  rw [he] at hte
  linarith

variable [PartialOrder A] [StarOrderedRing A] in
/-- **`c·s ∈ closure GL(A)` for `c ≥ 0` and `s` invertible.** -/
theorem nonneg_mul_mem_closure_invertibles {c s : A} (hc : 0 ≤ c) (hs : IsUnit s) :
    c * s ∈ closure (invertibles A) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hs0 : 0 ≤ ‖s‖ := norm_nonneg s
  have hs1 : 0 < ‖s‖ + 1 := by linarith
  set η : ℝ := ε / (2 * (‖s‖ + 1)) with hηdef
  have hη : 0 < η := by positivity
  refine ⟨(c + algebraMap ℝ A η) * s, (isUnit_add_algebraMap_of_nonneg hc hη).mul hs, ?_⟩
  rw [dist_eq_norm, add_mul, sub_add_cancel_left, norm_neg, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul, norm_smul, Real.norm_of_nonneg hη.le]
  calc η * ‖s‖ ≤ η * (‖s‖ + 1) := by nlinarith
    _ = ε / 2 := by
        rw [hηdef, div_mul_eq_mul_div, mul_div_mul_right _ _ hs1.ne']
    _ < ε := by linarith

end DistanceToInvertibles
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.DistanceToInvertibles.dense_invertibles_iff
#audit_axioms GroupApproximation.DistanceToInvertibles.distGL_le_spectralRadius
#audit_axioms GroupApproximation.DistanceToInvertibles.distGL_le_norm
#audit_axioms GroupApproximation.DistanceToInvertibles.distGL_mul_of_mem_unitary
#audit_axioms GroupApproximation.DistanceToInvertibles.nonneg_mul_mem_closure_invertibles
