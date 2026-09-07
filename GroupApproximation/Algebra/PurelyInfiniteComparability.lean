import GroupApproximation.Algebra.PurelyInfiniteBridge

/-!
# Comparability of idempotents, from single-sandwich division

Ara--Goodearl--Pardo's §1 develops the comparison theory of idempotents in a
purely infinite simple ring, and their §2 runs on it: both printed clauses of
`thm:mf-quotient-units`'s proof — the Menal--Moncasi reduction and Step 1 — begin
by choosing idempotents equivalent to prescribed ones inside a given corner.

The engine of that theory is **comparability**: inside any nonzero idempotent `e`
sits an idempotent equivalent to any prescribed idempotent `g`.  In the sandwich
form of pure infiniteness that is four lines, with explicit witnesses and no
comparison theory at all.

## The construction

Sandwich `e` to the unit: `x * e * y = 1`.  Then

    `f = e * y * g * x * e`

is idempotent, lies below `e`, and is equivalent to `g` via the pair
`(e * y * g, g * x * e)`.  Every step is a single use of `e * e = e`, `g * g = g`,
or `x * e * y = 1`.

## Why this is recorded here

It is the piece of Ara--Goodearl--Pardo §1 that §2 actually consumes, and having
it cheap changes what the remaining §2 citations cost.  It does **not** by itself
give either printed clause: those also need the generalised matrix-ring
description of `R` and a Gaussian elimination in it (clause (a)), and a ring
isomorphism `M_n(R) ≅ PRP` (clause (b)).  This module supplies their common
starting move and nothing more.
-/

namespace GroupApproximation
namespace MFQuotientUnits

section Comparability

variable {R : Type*} [Ring R]

/-- **Comparability.**  If every nonzero element sandwiches to `1`, then inside
any nonzero idempotent `e` there is an idempotent equivalent to any prescribed
idempotent `g`.

The witness is `f = e * y * g * x * e` for a sandwich `x * e * y = 1`. -/
theorem exists_idempotentLE_equivalent
    (hsand : ∀ a : R, a ≠ 0 → ∃ x y : R, x * a * y = 1)
    {e g : R} (he : IsIdempotentElem e) (hg : IsIdempotentElem g)
    (hene : e ≠ 0) :
    ∃ f : R, IsIdempotentElem f ∧ IdempotentLE f e ∧
      IsEquivalentIdempotent R f g := by
  obtain ⟨x, y, hxey⟩ := hsand e hene
  refine ⟨e * y * g * x * e, ?_, ⟨?_, ?_⟩, e * y * g, g * x * e, ?_, ?_⟩
  · -- idempotent: the middle `e * e` collapses, then `x * e * y = 1`, then `g * g = g`
    show e * y * g * x * e * (e * y * g * x * e) = e * y * g * x * e
    have e₁ : e * y * g * x * e * (e * y * g * x * e)
        = e * y * g * (x * (e * e) * y) * g * x * e := by noncomm_ring
    rw [e₁, he, hxey]
    have e₂ : e * y * g * 1 * g * x * e = e * y * (g * g) * x * e := by
      noncomm_ring
    rw [e₂, hg]
  · show e * (e * y * g * x * e) = e * y * g * x * e
    have e₁ : e * (e * y * g * x * e) = (e * e) * y * g * x * e := by noncomm_ring
    rw [e₁, he]
  · show e * y * g * x * e * e = e * y * g * x * e
    have e₁ : e * y * g * x * e * e = e * y * g * x * (e * e) := by noncomm_ring
    rw [e₁, he]
  · -- `f = (e * y * g) * (g * x * e)`, using `g * g = g`
    have e₁ : e * y * g * (g * x * e) = e * y * (g * g) * x * e := by noncomm_ring
    rw [e₁, hg]
  · -- `g = (g * x * e) * (e * y * g)`, using `e * e = e` then the sandwich
    have e₁ : g * x * e * (e * y * g) = g * (x * (e * e) * y) * g := by noncomm_ring
    rw [e₁, he, hxey]
    have e₂ : g * 1 * g = g * g := by noncomm_ring
    rw [e₂, hg]

/-- The comparable idempotent is nonzero whenever the prescribed one is. -/
theorem exists_idempotentLE_equivalent_ne_zero
    (hsand : ∀ a : R, a ≠ 0 → ∃ x y : R, x * a * y = 1)
    {e g : R} (he : IsIdempotentElem e) (hg : IsIdempotentElem g)
    (hene : e ≠ 0) (hgne : g ≠ 0) :
    ∃ f : R, IsIdempotentElem f ∧ IdempotentLE f e ∧
      IsEquivalentIdempotent R f g ∧ f ≠ 0 := by
  obtain ⟨f, hf, hle, hequiv⟩ :=
    exists_idempotentLE_equivalent hsand he hg hene
  exact ⟨f, hf, hle, hequiv,
    ne_zero_of_isEquivalentIdempotent hg hgne hequiv.symm⟩

end Comparability

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.exists_idempotentLE_equivalent

#audit_axioms GroupApproximation.MFQuotientUnits.exists_idempotentLE_equivalent_ne_zero
