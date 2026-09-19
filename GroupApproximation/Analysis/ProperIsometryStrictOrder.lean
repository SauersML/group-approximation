import Mathlib.Analysis.CStarAlgebra.Projection
import GroupApproximation.Analysis.ProperIsometryFromCompression

/-!
# Proper isometries from strict projection compression

The basic statement is:

> Let `A` be a unital C*-algebra containing a projection `p` and a unitary
> `u` with `p < u p u*`.  Then `A` contains an isometry that is not a
> unitary; consequently `A` is not stably finite and has no faithful tracial
> state.

`Analysis/ProperIsometryFromCompression` proves exactly this, but states the
hypothesis as the three ring identities `p (u p u*) = p`, `(u p u*) p = p`
and `u p u* ≠ p`, deliberately so that the calculation needs no order on
projections.  This file supplies the missing bridge, in both directions:

* `ProperProjectionCompression.mem_unitary_conj_isStarProjection` — the
  conjugate `u p u*` of a projection by a unitary is again a projection;
* `ProperProjectionCompression.lt_iff` — for projections, `p < u p u*` holds
  in the C*-order **exactly** when the three printed identities do.  The
  forward direction is `IsStarProjection.le_iff_mul_eq_left` and
  `le_iff_mul_eq_right` of Mathlib together with `LT.lt.ne'`; the backward
  direction is `lt_of_le_of_ne`;
* `ProperProjectionCompression.ofStrictLT` — the datum, built from the
  printed hypothesis alone;
* `manuscriptProperIsometryStrictOrder` — the printed proposition, header and
  all three conclusions, from `p < u p u*`.

Because the two forms are equivalent (`lt_iff`), the substitution the ledger
records for this proposition is now certified, not merely asserted.

## The order

The order is carried as the instance pair `[PartialOrder A]
[StarOrderedRing A]`, Mathlib's spelling of "the C*-order", which is how
`Analysis/KazhdanProjectionAbsorption` already states its order hypotheses.
The statement therefore holds for *every* compatible order, and the printed
one — `CStarAlgebra.spectralOrder`, supplied by `CStarAlgebra.spectralOrderedRing`
and used as a `local instance` in `Analysis/MaximalCStarProperCompression` —
is one of them.  Quantifying over the orders strengthens the statement; it
does not weaken it.
-/

namespace GroupApproximation

universe u

noncomputable section

namespace ProperProjectionCompression

variable {A : Type u} [CStarAlgebra A]

/-- The conjugate of a projection by a unitary is a projection. -/
theorem isStarProjection_unitary_conj {p u : A} (hp : IsStarProjection p)
    (hu : u ∈ unitary A) : IsStarProjection (u * p * star u) := by
  constructor
  · show (u * p * star u) * (u * p * star u) = u * p * star u
    calc (u * p * star u) * (u * p * star u)
        = u * (p * ((star u * u) * p)) * star u := by noncomm_ring
      _ = u * (p * ((1 : A) * p)) * star u := by rw [hu.1]
      _ = u * (p * p) * star u := by rw [one_mul]
      _ = u * p * star u := by rw [hp.isIdempotentElem]
  · show star (u * p * star u) = u * p * star u
    rw [star_mul, star_mul, star_star, hp.isSelfAdjoint.star_eq, mul_assoc]

section Order

variable [PartialOrder A] [StarOrderedRing A]

/-- **The printed hypothesis and the ring identities agree.**  For a
projection `p` and a unitary `u`, the strict inequality `p < u p u*` of the
C*-order is equivalent to the conjunction of the two absorption identities
and properness that `ProperProjectionCompression` records. -/
theorem lt_iff {p u : A} (hp : IsStarProjection p) (hu : u ∈ unitary A) :
    p < u * p * star u ↔
      (p * (u * p * star u) = p ∧ (u * p * star u) * p = p ∧
        u * p * star u ≠ p) := by
  have hq : IsStarProjection (u * p * star u) :=
    isStarProjection_unitary_conj hp hu
  constructor
  · intro hlt
    exact ⟨(hp.le_iff_mul_eq_left hq).mp hlt.le,
      (hp.le_iff_mul_eq_right hq).mp hlt.le, hlt.ne'⟩
  · rintro ⟨hleft, -, hne⟩
    exact lt_of_le_of_ne ((hp.le_iff_mul_eq_left hq).mpr hleft) (Ne.symm hne)

/-- A projection `p` and a unitary `u` with `p < u p u*` give a proper
projection compression, hence all the conclusions of
`Analysis/ProperIsometryFromCompression`. -/
def ofStrictLT {p u : A} (hp : IsStarProjection p) (hu : u ∈ unitary A)
    (hlt : p < u * p * star u) : ProperProjectionCompression A where
  p := p
  u := u
  p_star := hp.isSelfAdjoint.star_eq
  p_mul_p := hp.isIdempotentElem
  u_star_mul := hu.1
  u_mul_star := hu.2
  p_mul_conjugate := ((lt_iff hp hu).mp hlt).1
  conjugate_mul_p := ((lt_iff hp hu).mp hlt).2.1
  conjugate_ne := ((lt_iff hp hu).mp hlt).2.2

end Order

end ProperProjectionCompression

/-- **Strict projection compression produces a proper isometry.**

> Let `A` be a unital C*-algebra containing a projection `p` and a unitary
> `u` with `p < u p u*`.  Then `A` contains an isometry that is not a
> unitary; consequently `A` is not stably finite and has no faithful tracial
> state.

The three conclusions are the nonunitary isometry, the failure of stable
finiteness, and the absence of a faithful tracial state. -/
theorem manuscriptProperIsometryStrictOrder :
    ∀ (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
      (p u : A), IsStarProjection p → u ∈ unitary A →
      p < u * p * star u →
      (∃ s : A, star s * s = 1 ∧ ¬ IsUnit s) ∧
        ¬ IsStablyFiniteRing A ∧
        ¬ Nonempty (FaithfulTracialState A) := by
  intro A _ _ _ p u hp hu hlt
  -- `not_isStablyFiniteRing` and `no_faithfulTracialState` do not mention the
  -- datum in their conclusions, so it cannot be inferred from the goal and has
  -- to be named at every call site.
  let D := ProperProjectionCompression.ofStrictLT hp hu hlt
  exact ⟨⟨D.isometry, D.star_isometry_mul_isometry, D.isometry_not_isUnit⟩,
    D.not_isStablyFiniteRing, D.no_faithfulTracialState⟩

end

end GroupApproximation
