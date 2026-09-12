import Mathlib.Analysis.SpecialFunctions.Pow.NNRpow
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import GroupApproximation.Meta.AxiomGuard

/-!
# A norm comparison with subexponential constants does not move a spectral radius

Gerasimova--Osin, *On invertible elements in reduced `C*`-algebras of
acylindrically hyperbolic groups* (arXiv:1910.14524), Proposition 2.4, has two
halves.  The first is geometric: from a symmetric equivariant combing with
growth functions `γ` and `ρ` one gets, for `a ∈ ℂG` supported in `S ∩ B(n)`,

  `‖a‖ ≤ γ(ρ(n))^{3/2} ‖a‖₂`.

The second is not geometric at all: if `S` is a subsemigroup, so that the
comparison applies to every power `a^k` with a constant `c k`, and if
`lim_k c k^{1/k} = 1`, then `r(a) = r₂(a)` -- the `ℓ²`-spectral radius property
that Dykema--de la Harpe's Theorem 1.4 consumes.

This module is that second half, with the group, the algebra and the combing
removed.  What is left is a statement about three sequences of reals:

  `limsup_rpow_le_of_le_mul` : `u k ≤ c k * v k` and `c k^{1/k} → 1`
  imply `limsup u k^{1/k} ≤ limsup v k^{1/k}`.

Instantiating `u k = ‖a^k‖`, `v k = ‖a^k‖₂` and `c k = γ(ρ(nk))^{3/2}` turns the
printed inequality into `r(a) ≤ r₂(a)`, which is the whole content: the reverse
inequality `r₂ ≤ r` is termwise and is proved in the Gerasimova--Osin slice.

## Why the constants only have to be subexponential

Because the exponent is `1/k`.  A factor `c k` that grows polynomially, or in
any way with `c k^{1/k} → 1`, contributes `1` to the limit, so the two spectral
radii cannot be separated by it.  In Gerasimova--Osin's application `γ` and `ρ`
are bounded by linear functions, so `c k` is polynomial in `k`, comfortably
inside this.

## Boundedness hypotheses

`limsup` comparisons in Mathlib need the two side conditions that appear below;
they are not automatic and they are not free.  Both are available in the
intended application: for `u k = ‖a^k‖` the sequence `‖a^k‖^{1/k}` is bounded by
`max 1 ‖a‖`, and for `v k = ‖a^k‖₂` the sequence is nonnegative, which is what
cobounded-below means here.
-/

open Filter Topology

namespace GroupApproximation

/-- **A subexponential factor does not change the `1/k`-th-root `limsup`.**

If `u k ≤ c k * v k` with all three sequences nonnegative, and if
`c k ^ (1/k) → 1`, then `limsup u k ^ (1/k) ≤ limsup v k ^ (1/k)`.

This is the non-geometric half of Gerasimova--Osin's Proposition 2.4. -/
theorem limsup_rpow_le_of_le_mul {u v c : ℕ → ℝ}
    (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 ≤ v k) (hc : ∀ k, 0 ≤ c k)
    (hle : ∀ k, u k ≤ c k * v k)
    (hc1 : Tendsto (fun k : ℕ ↦ c k ^ ((k : ℝ)⁻¹)) atTop (𝓝 1))
    (hcob : IsCoboundedUnder (· ≤ ·) atTop (fun k : ℕ ↦ u k ^ ((k : ℝ)⁻¹)))
    (hbdd : IsBoundedUnder (· ≤ ·) atTop (fun k : ℕ ↦ v k ^ ((k : ℝ)⁻¹))) :
    limsup (fun k : ℕ ↦ u k ^ ((k : ℝ)⁻¹)) atTop
      ≤ limsup (fun k : ℕ ↦ v k ^ ((k : ℝ)⁻¹)) atTop := by
  set U : ℕ → ℝ := fun k ↦ c k ^ ((k : ℝ)⁻¹) with hU
  set V : ℕ → ℝ := fun k ↦ v k ^ ((k : ℝ)⁻¹) with hV
  have hUnonneg : ∀ k, 0 ≤ U k := fun k ↦ Real.rpow_nonneg (hc k) _
  have hVnonneg : ∀ k, 0 ≤ V k := fun k ↦ Real.rpow_nonneg (hv k) _
  have hUfreq : ∃ᶠ k : ℕ in atTop, 0 ≤ U k :=
    (Filter.Eventually.of_forall hUnonneg).frequently
  have hVev : 0 ≤ᶠ[atTop] V := Filter.Eventually.of_forall hVnonneg
  have hUbdd : IsBoundedUnder (· ≤ ·) atTop U := hc1.isBoundedUnder_le
  -- pointwise: the `1/k`-th root of the comparison
  have hpt : ∀ k : ℕ, u k ^ ((k : ℝ)⁻¹) ≤ (U * V) k := by
    intro k
    have h1 : u k ^ ((k : ℝ)⁻¹) ≤ (c k * v k) ^ ((k : ℝ)⁻¹) :=
      Real.rpow_le_rpow (hu k) (hle k) (by positivity)
    rwa [Real.mul_rpow (hc k) (hv k)] at h1
  -- the product sequence is bounded above
  have hprodbdd : IsBoundedUnder (· ≤ ·) atTop (U * V) :=
    isBoundedUnder_le_mul_of_nonneg hUfreq hUbdd hVev hbdd
  -- compare, then split the product
  have h1 : limsup (fun k : ℕ ↦ u k ^ ((k : ℝ)⁻¹)) atTop ≤ limsup (U * V) atTop :=
    limsup_le_limsup (Filter.Eventually.of_forall hpt) hcob hprodbdd
  have h2 : limsup (U * V) atTop ≤ limsup U atTop * limsup V atTop :=
    limsup_mul_le hUfreq hUbdd hVev hbdd
  have h3 : limsup U atTop = 1 := hc1.limsup_eq
  rw [h3, one_mul] at h2
  exact h1.trans h2

/-- **The two `1/k`-th-root `limsup`s agree**, when the comparison holds in one
direction with subexponential constants and termwise in the other.

This is the shape Gerasimova--Osin's Proposition 2.4 is used in: `v k ≤ u k`
termwise gives `r₂ ≤ r` for free, and the comparison `u k ≤ c k * v k` with
`c k ^ (1/k) → 1` gives the reverse. -/
theorem limsup_rpow_eq_of_le_mul {u v c : ℕ → ℝ}
    (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 ≤ v k) (hc : ∀ k, 0 ≤ c k)
    (hle : ∀ k, u k ≤ c k * v k) (hge : ∀ k, v k ≤ u k)
    (hc1 : Tendsto (fun k : ℕ ↦ c k ^ ((k : ℝ)⁻¹)) atTop (𝓝 1))
    (hcobu : IsCoboundedUnder (· ≤ ·) atTop (fun k : ℕ ↦ u k ^ ((k : ℝ)⁻¹)))
    (hcobv : IsCoboundedUnder (· ≤ ·) atTop (fun k : ℕ ↦ v k ^ ((k : ℝ)⁻¹)))
    (hbddu : IsBoundedUnder (· ≤ ·) atTop (fun k : ℕ ↦ u k ^ ((k : ℝ)⁻¹)))
    (hbddv : IsBoundedUnder (· ≤ ·) atTop (fun k : ℕ ↦ v k ^ ((k : ℝ)⁻¹))) :
    limsup (fun k : ℕ ↦ u k ^ ((k : ℝ)⁻¹)) atTop
      = limsup (fun k : ℕ ↦ v k ^ ((k : ℝ)⁻¹)) atTop := by
  refine le_antisymm
    (limsup_rpow_le_of_le_mul hu hv hc hle hc1 hcobu hbddv) ?_
  refine limsup_le_limsup (Filter.Eventually.of_forall fun k ↦ ?_) hcobv hbddu
  exact Real.rpow_le_rpow (hv k) (hge k) (by positivity)

end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.limsup_rpow_le_of_le_mul
#audit_axioms GroupApproximation.limsup_rpow_eq_of_le_mul
