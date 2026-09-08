import GroupApproximation.Algebra.PurelyInfiniteSimpleRing
import GroupApproximation.Meta.AxiomGuard

/-!
# Adding a common orthogonal complement preserves equivalence to `1`

`AGPStepOne`'s clause (b) sets `r_1 := 1 - e + f` for an idempotent `f ≤ e`
equivalent to `e`, and the matrix-unit construction needs `r_1` itself
equivalent to `1` (all `n` diagonal blocks of a matrix presentation must be
mutually equivalent).  This module supplies that: given a *normalised*
isometry pair for `e ~ f` (`exists_normalized_isometry`'s output: `t * s = e`,
`s * t = f`, both fixed by `e` on either side), `1 - e + f` is equivalent to
`1`, via the witnesses `1 - e + s`, `1 - e + t`.

## Why this holds

For `s, t` fixed by `e` on both sides (`e * s = s = s * e`, `e * t = t = t * e`),

    `(1 - e + t) * (1 - e + s) = (1-e)*(1-e) + (1-e)*s + t*(1-e) + t*s
      = (1-e) + 0 + 0 + e = 1`,

using `(1-e)*(1-e) = 1-e`, `(1-e)*s = s - e*s = 0`, `t*(1-e) = t - t*e = 0`, and
`t*s = e`.  The same computation with `s*t = f` in place of `t*s = e` gives
`(1-e+s)*(1-e+t) = 1-e+f`.  So `1-e+s`, `1-e+t` is an equivalence pair for
`1-e+f` and `1`.
-/

namespace GroupApproximation
namespace MFQuotientUnits

variable {R : Type*} [Ring R]

/-- **A common orthogonal complement transports equivalence to `1`.**  From a
normalised isometry pair for `e ~ f` (`f ≤ e`), `1 - e + f` is equivalent to
`1`. -/
theorem isEquivalentIdempotent_one_sub_add_of_normalized {e f s t : R}
    (he : IsIdempotentElem e) (hts : t * s = e) (hst : s * t = f)
    (hes : e * s = s) (hse : s * e = s) (het : e * t = t) (hte : t * e = t) :
    IsEquivalentIdempotent R (1 - e + f) 1 := by
  have h1e : (1 - e) * s = 0 := by
    have h1 : (1 - e) * s = s - e * s := by noncomm_ring
    rw [h1, hes, sub_self]
  have h2e : t * (1 - e) = 0 := by
    have h1 : t * (1 - e) = t - t * e := by noncomm_ring
    rw [h1, hte, sub_self]
  have h3e : s * (1 - e) = 0 := by
    have h1 : s * (1 - e) = s - s * e := by noncomm_ring
    rw [h1, hse, sub_self]
  have h4e : (1 - e) * t = 0 := by
    have h1 : (1 - e) * t = t - e * t := by noncomm_ring
    rw [h1, het, sub_self]
  have hee : (1 - e) * (1 - e) = 1 - e := IsIdempotentElem.one_sub he
  refine ⟨1 - e + s, 1 - e + t, ?_, ?_⟩
  · have h1 : (1 - e + s) * (1 - e + t)
        = (1 - e) * (1 - e) + (1 - e) * t + s * (1 - e) + s * t := by
      noncomm_ring
    rw [h1, hee, h4e, h3e, hst]
    abel
  · have h1 : (1 - e + t) * (1 - e + s)
        = (1 - e) * (1 - e) + (1 - e) * s + t * (1 - e) + t * s := by
      noncomm_ring
    rw [h1, hee, h1e, h2e, hts]
    abel

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.isEquivalentIdempotent_one_sub_add_of_normalized
