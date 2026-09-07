import GroupApproximation.Algebra.PurelyInfiniteComparability
import GroupApproximation.Algebra.PurelyInfiniteSandwich

/-!
# The ring's own unit is an infinite idempotent

Ara--Goodearl--Pardo Theorem 2.4 Step 1 (`AGPStepOne`) builds, for a nonzero
idempotent `e` and `n ≥ 2`, an idempotent `f < e` equivalent to `e` and
orthogonal idempotents `r_2, …, r_n ≤ e - f`, **each equivalent to `1`**, so
that a ring isomorphism `θ : M_n(R) → PRP` can be built.  Every one of those
`r_i` is a proper sub-idempotent of `R` equivalent to the *whole ring's own
unit* — which is only possible because `1` itself is properly infinite.

That is what this module proves: `1` is an infinite idempotent of any purely
infinite simple ring, with no extra hypothesis.  It is the base case that lets
comparability be applied with `1` as the *prescribed* idempotent, over and over,
to peel off as many disjoint copies of `1` as a construction needs.

## The proof

`R` contains some infinite idempotent `e₀` (`exists_infiniteIdempotent_of_nontrivial`).
Comparability, applied with `e₀` as the ambient idempotent and `1` as the
prescribed one, gives `f ≤ e₀` with `f ~ 1`.

* If `f = 1`, then `f ≤ e₀` forces `e₀ = 1`, and `e₀`'s own infinite
  decomposition already is `1`'s.
* If `f ≠ 1`, then `1 = f + (1 - f)` is the infinite decomposition of `1`
  directly: `f ~ 1` and `1 - f ≠ 0`.

Either way `1` is infinite; no case split is visible in the final statement.
-/

namespace GroupApproximation
namespace MFQuotientUnits

variable {R : Type*} [Ring R]

/-- **The unit of a purely infinite simple ring is itself an infinite
idempotent.**  Needed so that comparability can be run with `1` as the
prescribed idempotent: fitting a copy of the *whole ring* inside a proper
corner is only sensible once `1` is known to be properly infinite. -/
theorem isInfiniteIdempotent_one (hR : IsPurelyInfiniteSimpleRing R) :
    IsInfiniteIdempotent R (1 : R) := by
  haveI := hR.isSimpleRing
  obtain ⟨e0, he0, hinf0⟩ := hR.exists_infiniteIdempotent_of_nontrivial
  have hsand : ∀ a : R, a ≠ 0 → ∃ x y : R, x * a * y = 1 :=
    fun a ha => exists_sandwich_of_isPurelyInfiniteSimpleRing hR ha
  obtain ⟨f, hf, hle, hequiv⟩ :=
    exists_idempotentLE_equivalent hsand he0 IsIdempotentElem.one hinf0.ne_zero
  rcases eq_or_ne f 1 with hf1 | hf1
  · have he0eq : e0 = 1 := by
      have h1 : e0 * 1 = 1 := by rw [hf1] at hle; exact hle.1
      simpa using h1
    rwa [he0eq] at hinf0
  · exact ⟨f, 1 - f, hf, hf.one_sub, hf.mul_one_sub_self, hf.one_sub_mul_self,
      by abel, hequiv.symm, sub_ne_zero.mpr hf1.symm⟩

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.isInfiniteIdempotent_one
