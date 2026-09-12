import GroupApproximation.Algebra.PurelyInfiniteSimpleRing
import GroupApproximation.Meta.AxiomGuard

/-!
# `1 - e + f` is orthogonal to anything below `e - f`

`AGPStepOne`'s clause (b) sets `r_1 := 1 - e + f` (for `f ≤ e`) and needs
`r_1` orthogonal to each of `r_2, …, r_n`, which are built below `e - f`.
This module supplies that orthogonality from `g ≤ e - f` alone — `f ≤ e` is
not needed:

    `(1 - e + f) * g = (1 - e) * g + f * g = (g - e*g) + f*g = 0`,

using `e*g - f*g = g` (from `g ≤ e - f`) to see `g - e*g = -f*g`.  The mirror
computation gives `g * (1 - e + f) = 0`.
-/

namespace GroupApproximation
namespace MFQuotientUnits

variable {R : Type*} [Ring R]

/-- **`1 - e + f` is orthogonal to any `g` below `e - f`**, given `f ≤ e`. -/
theorem one_sub_add_orthogonal_of_le_sub {e f g : R}
    (hg1 : g * (e - f) = g) (hg2 : (e - f) * g = g) :
    (1 - e + f) * g = 0 ∧ g * (1 - e + f) = 0 := by
  have h1 : g * (e - f) = g * e - g * f := by noncomm_ring
  have h2 : (e - f) * g = e * g - f * g := by noncomm_ring
  rw [h1] at hg1
  rw [h2] at hg2
  constructor
  · have h3 : (1 - e + f) * g = (g - e * g) + f * g := by noncomm_ring
    rw [h3]
    have h4 : g - e * g = -(f * g) := by
      have h5 : e * g = g + f * g := sub_eq_iff_eq_add.mp hg2
      rw [h5]; abel
    rw [h4]; abel
  · have h3 : g * (1 - e + f) = (g - g * e) + g * f := by noncomm_ring
    rw [h3]
    have h4 : g - g * e = -(g * f) := by
      have h5 : g * e = g + g * f := sub_eq_iff_eq_add.mp hg1
      rw [h5]; abel
    rw [h4]; abel

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.one_sub_add_orthogonal_of_le_sub
