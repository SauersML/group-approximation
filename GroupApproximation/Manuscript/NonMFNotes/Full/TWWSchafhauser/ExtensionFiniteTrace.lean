import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Group.Hom.Defs

/-!
# A faithful trace rules out Cuntz pairs

Lane TWWSchafhauser-3c (work order WO-TWWCore-3, piece 3c).  Manuscript:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378).

The direct sum of extensions in the Elliott--Kucerovsky absorption framework is
implemented by a pair of isometries `s₁, s₂` with `s₁⋆ s₁ = s₂⋆ s₂ = 1` and
`s₁ s₁⋆ + s₂ s₂⋆ = 1` in the algebra that receives the Busby map (G. A. Elliott and
D. Kucerovsky, *An abstract Voiculescu--Brown--Douglas--Fillmore absorption theorem*,
Pacific J. Math. **198** (2001), §1).  That algebra is the corona `M(J)/J` of the
ideal.  This file records why it cannot be the tracial quotient `Q^ω` of
Schafhauser's trace-kernel extension (J. reine angew. Math. **759** (2020), §3--5),
nor any other unital ring with a faithful trace.

* `mul_star_self_eq_one_of_faithful_trace`: under a faithful trace, every isometry
  is a coisometry.
* `false_of_isometry_pair_of_faithful_trace`: under a faithful trace, in a nontrivial
  ring, there is no Cuntz pair.

Everything is purely algebraic.  The trace is an additive map `τ : Q →+ M` with
`τ (x * y) = τ (y * x)` that is faithful on the elements `x⋆ x`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

/-- **Under a faithful trace, isometries are unitaries.**  If `s⋆ s = 1`, then
`1 - s s⋆` is a projection with trace `τ 1 - τ (s⋆ s) = 0`, so it vanishes. -/
theorem mul_star_self_eq_one_of_faithful_trace {Q M : Type*} [Ring Q] [StarRing Q]
    [AddCommGroup M] (τ : Q →+ M) (hτ : ∀ x y : Q, τ (x * y) = τ (y * x))
    (hτf : ∀ x : Q, τ (star x * x) = 0 → x = 0) {s : Q} (hs : star s * s = 1) :
    s * star s = 1 := by
  have hp : star (1 - s * star s) * (1 - s * star s) = 1 - s * star s := by
    rw [star_sub, star_one, star_mul, star_star, sub_mul, one_mul, mul_sub, mul_one,
      mul_assoc s (star s) (s * star s), ← mul_assoc (star s) s (star s), hs, one_mul,
      sub_self, sub_zero]
  have ht : τ (1 - s * star s) = 0 := by
    rw [map_sub, hτ s (star s), hs, sub_self]
  have h0 : 1 - s * star s = 0 := hτf (1 - s * star s) (by rw [hp]; exact ht)
  exact (sub_eq_zero.mp h0).symm

/-- **There is no Cuntz pair under a faithful trace.**  If `s₁, s₂` are isometries
with `s₁ s₁⋆ + s₂ s₂⋆ = 1`, then `s₁ s₁⋆ = 1`, so `s₂ s₂⋆ = 0`.  But `s₂ s₂⋆ = 1`
as well, which contradicts `1 ≠ 0`.  So a Busby map into a tracial quotient such as
`Q^ω` cannot carry the Elliott--Kucerovsky direct sum.  The sum lives in the
corona of the ideal. -/
theorem false_of_isometry_pair_of_faithful_trace {Q M : Type*} [Ring Q] [StarRing Q]
    [Nontrivial Q] [AddCommGroup M] (τ : Q →+ M) (hτ : ∀ x y : Q, τ (x * y) = τ (y * x))
    (hτf : ∀ x : Q, τ (star x * x) = 0 → x = 0) {s₁ s₂ : Q} (h₁ : star s₁ * s₁ = 1)
    (h₂ : star s₂ * s₂ = 1) (hsum : s₁ * star s₁ + s₂ * star s₂ = 1) : False := by
  rw [mul_star_self_eq_one_of_faithful_trace τ hτ hτf h₁] at hsum
  have h0 : s₂ * star s₂ = 0 := add_left_cancel (hsum.trans (add_zero (1 : Q)).symm)
  exact one_ne_zero ((mul_star_self_eq_one_of_faithful_trace τ hτ hτf h₂).symm.trans h0)

end GroupApproximation.Full.TWWSchafhauser
