import GroupApproximation.Algebra.PurelyInfiniteUnitInfinite
import GroupApproximation.Manuscript.OneSidedMFRadical.MFHomKernel

/-!
# The corner-unit subgroup, taking the corner to be the whole ring

`Algebra/PurelyInfiniteCornerSandwich.lean` places elements of a *proper*
corner's elementary group inside `cornerUnitSubgroup R`.  `AGPStepOne`'s
Menal--Moncasi construction instead builds a ring isomorphism
`θ : M_n(R) → PRP` whose *source* is the matrix ring over `R` itself (entries
equivalent to `1`, not to a smaller idempotent), so the corner playing the role
of `S` in `cornerUnitSubgroup`'s definition is `R` itself.

This is in fact simpler than the proper-corner case: `R` is already simple, so
fullness of `1 - s * t` needs no infinite-idempotent bookkeeping at all, only
simplicity (`isFiniteMultipleSum_one_of_isSimpleRing`).  The one thing still
needed is a genuine proper isometry pair for the unit `1` itself
(`t * s = 1 ≠ s * t`), which is exactly `isInfiniteIdempotent_one`'s own
construction, extracted here as a standalone fact.
-/

namespace GroupApproximation
namespace MFQuotientUnits

variable {R : Type*} [Ring R]

/-- **A proper isometry pair for the unit itself.**  `t * s = 1` and
`s * t ≠ 1`, so `1 - s * t ≠ 0`. -/
theorem exists_unitProperIsometry (hR : IsPurelyInfiniteSimpleRing R) :
    ∃ s t : R, t * s = 1 ∧ (1 : R) - s * t ≠ 0 := by
  obtain ⟨f₀, g₀, hf₀, hg₀, hf₀g₀, hg₀f₀, hsum₀, hequiv₀, hg₀ne⟩ :=
    isInfiniteIdempotent_one hR
  obtain ⟨s₀, t₀, hts₀, hst₀, -, -, -, -⟩ :=
    exists_normalized_isometry IsIdempotentElem.one hf₀ (one_mul f₀) (mul_one f₀)
      hequiv₀
  refine ⟨s₀, t₀, hts₀, ?_⟩
  rw [hst₀]
  intro hcon
  exact hg₀ne (by
    have h1 : (1 : R) - f₀ = g₀ := by rw [hsum₀]; abel
    rw [hcon] at h1
    simpa using h1.symm)

/-- **`cornerUnitSubgroup` taking the corner to be the whole ring.**  Every
image of an elementary group `EL_n(R)`, `n ≥ 2`, lands in `cornerUnitSubgroup
R` — no infinite idempotent needed, only simplicity. -/
theorem elementaryRange_le_cornerUnitSubgroup {R : Type} [Ring R] [Countable R]
    (hR : IsPurelyInfiniteSimpleRing R) {n : ℕ} (hn : 2 ≤ n)
    (φ : elementaryGroup (Fin n) R →* Rˣ) : φ.range ≤ cornerUnitSubgroup R := by
  haveI := hR.isSimpleRing
  obtain ⟨s, t, hts, hne⟩ := exists_unitProperIsometry hR
  have hfull : ∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1 := by
    obtain ⟨m, a, b, hab⟩ := isFiniteMultipleSum_one_of_isSimpleRing hne
    exact ⟨m, a, b, hab.symm⟩
  exact le_cornerUnitSubgroup R s t hts hfull n hn φ

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.exists_unitProperIsometry
#audit_axioms GroupApproximation.MFQuotientUnits.elementaryRange_le_cornerUnitSubgroup
