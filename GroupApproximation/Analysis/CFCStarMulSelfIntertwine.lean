import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Algebra.Polynomial
import GroupApproximation.Meta.AxiomGuard

/-!
# Intertwining `x^*x` and `xx^*` through the continuous functional calculus

For an element `x` of a unital C⋆-algebra and a continuous real function `f`,

    `x · f(x^*x) = f(xx^*) · x`.

This is the identity `v g(|x|) = g(|x^*|) v` of the polar decomposition `x = v|x|`,
written without `v`, which in general does not belong to the algebra.  It is what
lets the distance estimates of Farah and Rørdam (`Analysis/RordamDistanceOne`) run on
the continuous functional calculus alone: no spectral projection and no polar
decomposition occurs anywhere.

The proof is the direct one.  On powers the identity is `x (x^*x)^n = (xx^*)^n x`, so
it holds for every polynomial.  Both spectra lie in one compact interval, where the
polynomials are uniformly dense (Weierstrass), and both sides move by at most
`‖x‖ · sup |f − q|` when `f` is replaced by a polynomial `q` (`norm_cfc_le`).

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` (stable rank one of `C*_r(Q)`, the
Gerasimova–Osin citation, proved along Dykema–Haagerup–Rørdam).  Certifies no printed
sentence on its own.
-/

namespace GroupApproximation
namespace CFCIntertwine

open Polynomial

variable {A : Type*} [CStarAlgebra A]

/-- `x (x^*x)^n = (xx^*)^n x`. -/
theorem mul_pow_star_mul_self (x : A) (n : ℕ) :
    x * (star x * x) ^ n = (x * star x) ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc x * (star x * x) ^ (n + 1) = x * (star x * x) ^ n * (star x * x) := by
          rw [pow_succ, ← mul_assoc]
      _ = (x * star x) ^ n * x * (star x * x) := by rw [ih]
      _ = (x * star x) ^ n * (x * star x) * x := by simp only [mul_assoc]
      _ = (x * star x) ^ (n + 1) * x := by rw [pow_succ]

/-- The intertwining identity for real polynomials. -/
theorem mul_aeval_star_mul_self (x : A) (q : ℝ[X]) :
    x * aeval (star x * x) q = aeval (x * star x) q * x := by
  refine Polynomial.induction_on' q (fun p r hp hr => ?_) (fun n c => ?_)
  · rw [map_add, map_add, mul_add, add_mul, hp, hr]
  · rw [aeval_monomial, aeval_monomial, ← mul_assoc, ← Algebra.commutes, mul_assoc,
      mul_pow_star_mul_self, ← mul_assoc]

/-- **`x · f(x^*x) = f(xx^*) · x`** for every continuous real function `f`. -/
theorem mul_cfc_star_mul_self (x : A) (f : ℝ → ℝ) (hf : Continuous f) :
    x * cfc f (star x * x) = cfc f (x * star x) * x := by
  obtain hA | hA := subsingleton_or_nontrivial A
  · exact Subsingleton.elim _ _
  have hsa₁ : IsSelfAdjoint (star x * x) := IsSelfAdjoint.star_mul_self x
  have hsa₂ : IsSelfAdjoint (x * star x) := by
    simpa only [star_star] using IsSelfAdjoint.star_mul_self (star x)
  set R : ℝ := ‖star x * x‖ + ‖x * star x‖ with hRdef
  have hR₁ : ∀ t ∈ spectrum ℝ (star x * x), t ∈ Set.Icc (-R) R := by
    intro t ht
    have h := spectrum.norm_le_norm_of_mem ht
    rw [Real.norm_eq_abs] at h
    have hn : 0 ≤ ‖x * star x‖ := norm_nonneg _
    rw [Set.mem_Icc]
    constructor
    · linarith [neg_abs_le t]
    · linarith [le_abs_self t]
  have hR₂ : ∀ t ∈ spectrum ℝ (x * star x), t ∈ Set.Icc (-R) R := by
    intro t ht
    have h := spectrum.norm_le_norm_of_mem ht
    rw [Real.norm_eq_abs] at h
    have hn : 0 ≤ ‖star x * x‖ := norm_nonneg _
    rw [Set.mem_Icc]
    constructor
    · linarith [neg_abs_le t]
    · linarith [le_abs_self t]
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_gt_imp_ge_of_dense fun ε hε => ?_
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  set δ : ℝ := ε / (2 * ‖x‖ + 1) with hδdef
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn (-R) R f hf.continuousOn δ hδ
  have hpoly := mul_aeval_star_mul_self x q
  rw [← cfc_polynomial q (star x * x) hsa₁, ← cfc_polynomial q (x * star x) hsa₂] at hpoly
  have hbound : ∀ a : A, (∀ t ∈ spectrum ℝ a, t ∈ Set.Icc (-R) R) →
      ‖cfc f a - cfc q.eval a‖ ≤ δ := by
    intro a hspec
    rw [← cfc_sub f q.eval a hf.continuousOn q.continuous.continuousOn]
    refine norm_cfc_le hδ.le fun t ht => ?_
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact (hq t (hspec t ht)).le
  have hsplit : x * cfc f (star x * x) - cfc f (x * star x) * x
      = x * (cfc f (star x * x) - cfc q.eval (star x * x))
        - (cfc f (x * star x) - cfc q.eval (x * star x)) * x := by
    rw [mul_sub, sub_mul, hpoly]
    abel
  rw [hsplit]
  calc ‖x * (cfc f (star x * x) - cfc q.eval (star x * x))
        - (cfc f (x * star x) - cfc q.eval (x * star x)) * x‖
      ≤ ‖x‖ * δ + δ * ‖x‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_left (hbound _ hR₁) hx0)
        · exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (hbound _ hR₂) hx0)
    _ ≤ ε := by
        have h2 : ‖x‖ * δ + δ * ‖x‖ = ε * (2 * ‖x‖) / (2 * ‖x‖ + 1) := by
          rw [hδdef]
          ring
        rw [h2, div_le_iff₀ (by positivity)]
        nlinarith

/-- `x · f(x^*x) · x^* = (u ↦ f(u)·u)(xx^*)`. -/
theorem mul_cfc_star_mul_self_mul_star (x : A) (f : ℝ → ℝ) (hf : Continuous f) :
    x * cfc f (star x * x) * star x = cfc (fun u => f u * u) (x * star x) := by
  have hsa₂ : IsSelfAdjoint (x * star x) := by
    simpa only [star_star] using IsSelfAdjoint.star_mul_self (star x)
  have h := cfc_mul f (fun u : ℝ => u) (x * star x) hf.continuousOn continuousOn_id
  rw [cfc_id' ℝ (x * star x) hsa₂] at h
  rw [mul_cfc_star_mul_self x f hf, mul_assoc, ← h]

/-- The adjoint form: `f(x^*x) · x^* = x^* · f(xx^*)`. -/
theorem cfc_star_mul_self_mul_star' (x : A) (f : ℝ → ℝ) (hf : Continuous f) :
    cfc f (star x * x) * star x = star x * cfc f (x * star x) := by
  have h := congrArg star (mul_cfc_star_mul_self x f hf)
  rwa [star_mul, star_mul, (cfc_predicate f (star x * x) : IsSelfAdjoint _).star_eq,
    (cfc_predicate f (x * star x) : IsSelfAdjoint _).star_eq] at h

/-- `f(a) · a · g(a) = (u ↦ f(u)·u·g(u))(a)` for a self-adjoint `a`. -/
theorem cfc_mul_self_mul_cfc (a : A) (ha : IsSelfAdjoint a) (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    cfc f a * a * cfc g a = cfc (fun u => f u * u * g u) a := by
  have h1 := cfc_mul f (fun u : ℝ => u) a hf.continuousOn continuousOn_id
  rw [cfc_id' ℝ a ha] at h1
  have h2 := cfc_mul (fun u : ℝ => f u * u) g a (hf.mul continuous_id).continuousOn
    hg.continuousOn
  rw [← h1, ← h2]

end CFCIntertwine
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CFCIntertwine.mul_pow_star_mul_self
#audit_axioms GroupApproximation.CFCIntertwine.mul_aeval_star_mul_self
#audit_axioms GroupApproximation.CFCIntertwine.mul_cfc_star_mul_self
#audit_axioms GroupApproximation.CFCIntertwine.mul_cfc_star_mul_self_mul_star
#audit_axioms GroupApproximation.CFCIntertwine.cfc_star_mul_self_mul_star'
#audit_axioms GroupApproximation.CFCIntertwine.cfc_mul_self_mul_cfc
