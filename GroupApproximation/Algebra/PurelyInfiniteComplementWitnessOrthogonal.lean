import GroupApproximation.Algebra.PurelyInfiniteComplementEquivalence

/-!
# `r_1`'s witnesses are orthogonal to `e - f` itself

`AGPStepOne` combines `r_1 = 1 - e + f` (built from a normalised isometry pair
`e ~ f`) with `r_2, …, r_n`, transported inside `e - f` by
`exists_matrixUnitWitnesses_within'`.  That transport guarantees the
*witnesses* `s' i, t' i` are individually absorbed by `e - f`
(`(e - f) * s' i = s' i`, `t' i * (e - f) = t' i`), which turns the needed
cross-orthogonality with `r_1`'s own witnesses `1 - e + t_f`, `1 - e + s_f`
into a one-line consequence of a single fact about the two constructions
meeting at `e - f`:

    `(1 - e + t_f) * (e - f) = 0`  and  `(e - f) * (1 - e + s_f) = 0`.

This module proves that fact, and the two general absorption-to-orthogonality
lemmas that turn it (together with `exists_matrixUnitWitnesses_within'`'s
guarantee) into the needed `t_1 * s' i = 0`, `t' i * s_1 = 0`.

## Why the two identities hold

`(1 - e) * (e - f) = 0` outright (both idempotent, `f ≤ e`), and
`t_f * (e - f) = t_f * e - t_f * f = t_f - t_f = 0`, using `t_f * e = t_f` and
`t_f * f = t_f * (s_f * t_f) = (t_f * s_f) * t_f = e * t_f = t_f`.  The mirror
computation gives the other identity.
-/

namespace GroupApproximation
namespace MFQuotientUnits

variable {R : Type*} [Ring R]

/-- **`r_1`'s witnesses annihilate `e - f` on the side facing `r_2, …, r_n`.** -/
theorem one_sub_add_mul_sub_eq_zero {e f sf tf : R} (he : IsIdempotentElem e)
    (htsf : tf * sf = e) (hstf : sf * tf = f) (hesf : e * sf = sf)
    (hsef : sf * e = sf) (hetf : e * tf = tf) (htef : tf * e = tf) :
    (1 - e + tf) * (e - f) = 0 ∧ (e - f) * (1 - e + sf) = 0 := by
  have htff : tf * f = tf := by
    calc tf * f = tf * (sf * tf) := by rw [hstf]
      _ = (tf * sf) * tf := by noncomm_ring
      _ = e * tf := by rw [htsf]
      _ = tf := hetf
  have hfsf : f * sf = sf := by
    calc f * sf = (sf * tf) * sf := by rw [hstf]
      _ = sf * (tf * sf) := by noncomm_ring
      _ = sf * e := by rw [htsf]
      _ = sf := hsef
  constructor
  · have h1 : (1 - e + tf) * (e - f) = (1 - e) * (e - f) + tf * (e - f) := by
      noncomm_ring
    rw [h1]
    have h2 : (1 - e) * (e - f) = e - f - e * e + e * f := by noncomm_ring
    have h3 : e * f = f := by
      calc e * f = e * (sf * tf) := by rw [hstf]
        _ = (e * sf) * tf := by noncomm_ring
        _ = sf * tf := by rw [hesf]
        _ = f := hstf
    rw [h2, he, h3]
    have h4 : e - f - e + f = 0 := by abel
    rw [h4]
    have h5 : tf * (e - f) = tf * e - tf * f := by noncomm_ring
    rw [h5, htef, htff, sub_self, zero_add]
  · have h1 : (e - f) * (1 - e + sf) = (e - f) * (1 - e) + (e - f) * sf := by
      noncomm_ring
    rw [h1]
    have h2 : (e - f) * (1 - e) = e - e * e - f + f * e := by noncomm_ring
    have h3 : f * e = f := by
      calc f * e = (sf * tf) * e := by rw [hstf]
        _ = sf * (tf * e) := by noncomm_ring
        _ = sf * tf := by rw [htef]
        _ = f := hstf
    rw [h2, he, h3]
    have h4 : e - e - f + f = 0 := by abel
    rw [h4]
    have h5 : (e - f) * sf = e * sf - f * sf := by noncomm_ring
    rw [h5, hesf, hfsf, sub_self, zero_add]

/-- **Absorption on the right, plus vanishing on the left, gives a vanishing
cross term.** -/
theorem mul_eq_zero_of_right_absorb {x g s : R} (hxg : x * g = 0)
    (hgs : g * s = s) : x * s = 0 := by
  calc x * s = x * (g * s) := by rw [hgs]
    _ = (x * g) * s := by noncomm_ring
    _ = 0 * s := by rw [hxg]
    _ = 0 := zero_mul _

/-- **Absorption on the left, plus vanishing on the right, gives a vanishing
cross term.** -/
theorem mul_eq_zero_of_left_absorb {t g y : R} (htg : t * g = t)
    (hgy : g * y = 0) : t * y = 0 := by
  calc t * y = (t * g) * y := by rw [htg]
    _ = t * (g * y) := by noncomm_ring
    _ = t * 0 := by rw [hgy]
    _ = 0 := mul_zero _

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.one_sub_add_mul_sub_eq_zero
#audit_axioms GroupApproximation.MFQuotientUnits.mul_eq_zero_of_right_absorb
#audit_axioms GroupApproximation.MFQuotientUnits.mul_eq_zero_of_left_absorb
