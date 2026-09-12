import GroupApproximation.Manuscript.NonMF.GerasimovaOsinTheorem11Slice

/-!
# The `ℓ²`-spectral radius property is one inequality

Dykema and de la Harpe's criterion asks that `r₂(a) = r(a)` for the elements of
`ℂG` supported on a free subsemigroup.  Half of that equality is free: the
`ℓ²`-norm never exceeds the operator norm, so

    r₂(a) ≤ r(a)

always, and the criterion's hypothesis is the single inequality `r(a) ≤ r₂(a)`.
This module proves that half.

## What it takes

`reducedTwoNorm_pow_rpow_le` gives the termwise comparison
`‖aᵏ‖₂^{1/k} ≤ ‖aᵏ‖^{1/k}`, and `limsup` is monotone once the two side
conditions are supplied:

* the smaller sequence is bounded below by `0`, which makes it coboundedly
  bounded above;
* the larger sequence is bounded above by `max 1 ‖a‖`, because
  `‖aᵏ‖ ≤ ‖a‖ᵏ` for `k ≥ 1` and the exponent `1/k` is `0` at `k = 0`.

Nothing here is deep; it is recorded because it halves the work in
`AllSupportedHaveL2SpectralRadiusProperty` and because the reverse inequality is
the one Gerasimova and Osin's Proposition 2.4 is for.

## Manuscript status

Infrastructure toward `DykemaDeLaHarpeTheorem14`; certifies no printed sentence
on its own.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.ReducedGroupCStarTrace
open Filter

universe u

/-- The `ℓ²`-spectral radius sequence is bounded below by zero. -/
theorem isCoboundedUnder_l2SpectralRadius {G : Type u} [Group G]
    (x : ReducedGroupCStar G) :
    IsCoboundedUnder (· ≤ ·) atTop
      (fun k : ℕ ↦ reducedTwoNorm (x ^ k) ^ ((k : ℝ)⁻¹)) :=
  isCoboundedUnder_le_of_le atTop
    (fun k ↦ Real.rpow_nonneg (reducedTwoNorm_nonneg (x ^ k)) _)

/-- The spectral-radius sequence is bounded above by `max 1 ‖a‖`. -/
theorem isBoundedUnder_operatorSpectralRadius {G : Type u} [Group G]
    (x : ReducedGroupCStar G) :
    IsBoundedUnder (· ≤ ·) atTop (fun k : ℕ ↦ ‖x ^ k‖ ^ ((k : ℝ)⁻¹)) := by
  refine isBoundedUnder_of ⟨max 1 ‖x‖, fun k ↦ ?_⟩
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [Nat.cast_zero, inv_zero, Real.rpow_zero]
    exact le_max_left _ _
  · have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    calc ‖x ^ k‖ ^ ((k : ℝ)⁻¹)
        ≤ (‖x‖ ^ k) ^ ((k : ℝ)⁻¹) :=
          Real.rpow_le_rpow (norm_nonneg _) (norm_pow_le' x hk) (by positivity)
      _ = ‖x‖ := by
          rw [← Real.rpow_natCast ‖x‖ k, ← Real.rpow_mul (norm_nonneg x),
            mul_inv_cancel₀ hkne, Real.rpow_one]
      _ ≤ max 1 ‖x‖ := le_max_right _ _

/-- **`r₂(a) ≤ r(a)` always.** -/
theorem l2SpectralRadius_le_operatorSpectralRadius {G : Type u} [Group G]
    (x : ReducedGroupCStar G) :
    l2SpectralRadius x ≤ operatorSpectralRadius x :=
  limsup_le_limsup
    (Filter.Eventually.of_forall (fun k ↦ reducedTwoNorm_pow_rpow_le x k))
    (isCoboundedUnder_l2SpectralRadius x)
    (isBoundedUnder_operatorSpectralRadius x)

/-- **The `ℓ²`-spectral radius property is the single inequality
`r(a) ≤ r₂(a)`.** -/
theorem hasL2SpectralRadiusProperty_iff {G : Type u} [Group G]
    (x : ReducedGroupCStar G) :
    HasL2SpectralRadiusProperty x
      ↔ operatorSpectralRadius x ≤ l2SpectralRadius x := by
  constructor
  · intro h
    exact le_of_eq h.symm
  · intro h
    exact le_antisymm (l2SpectralRadius_le_operatorSpectralRadius x) h

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

#audit_axioms l2SpectralRadius_le_operatorSpectralRadius
#audit_axioms hasL2SpectralRadiusProperty_iff
