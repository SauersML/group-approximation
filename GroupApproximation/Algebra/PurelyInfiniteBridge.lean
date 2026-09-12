import GroupApproximation.Algebra.PurelyInfiniteSimpleMatrix

/-!
# From the sandwich form of pure infiniteness to the idempotent form

This repository carries two predicates for "purely infinite simple", in two
vocabularies, and until now nothing connected them:

* `Algebra/PurelyInfiniteSimpleRing.lean`'s `IsPurelyInfiniteSimpleRing` — the
  **idempotent** form, printed by Ara--Goodearl--Pardo, Definitions 1.2: simple,
  and every nonzero right ideal contains an infinite idempotent.  This is the
  one `thm:mf-quotient-units` and `AGPMatrixReduction` consume.
* `Manuscript/OneSidedMFRadical/PartialClosureAnalysis.lean`'s
  `IsPurelyInfiniteSimpleUnitalRing` — the **sandwich** form: simple, not a
  division ring, and every nonzero element sandwiches to `1`.  This is the one
  the tree actually proves of concrete rings, `L_{𝔽₂}(1,2)` among them.

`PurelyInfiniteSimpleRing.lean`'s own docstring records the gap: for a unital
simple ring the two agree, "but that equivalence is a theorem of
Ara--Goodearl--Pardo and not a rewriting, so neither predicate is stated in terms
of the other here".

## What this module proves, and what it costs

The direction the manuscript needs — sandwich to idempotent — turns out **not**
to need Ara--Goodearl--Pardo §1, given
`Algebra/PurelyInfiniteSimpleMatrix.lean`'s `IsInfiniteIdempotent.of_equivalent`.
The argument is two steps:

* A **proper isometry** `t * s = 1`, `s * t ≠ 1` makes `1` an infinite
  idempotent outright: `1 = st + (1 - st)`, the two halves are orthogonal
  idempotents, `1` is equivalent to `st` via the pair `(t, s)`, and `1 - st ≠ 0`
  is exactly `s * t ≠ 1`.
* The sandwich `x * a * y = 1` makes `e = a * (y * x)` an idempotent **in `aR`**
  that is equivalent to `1`, via the pair `(a * y, x)`.  Infiniteness is an
  invariant of equivalence, so `e` is infinite.

So every nonzero `a` yields an infinite idempotent in `aR`, which is the
idempotent form.

## The one thing this does not do

The sandwich predicate's middle clause is "`R` is not a division ring", and that
clause does **not** by itself produce a proper isometry: a nonzero non-unit may
still be one-sided invertible.  Deriving the isometry from non-division-ring-ness
is the part of the Ara--Goodearl--Pardo equivalence that stays unformalized.  So
the isometry is an explicit hypothesis here, not something extracted from the
sandwich predicate.

That costs nothing in practice: the isometry is exactly the datum the tree's
concrete rings already carry — `OneSidedCompressor.OneSidedInverse` is a `t * s = 1`
pair, and `PartialClosureAnalysis.lean` derives non-division-ring-ness of the
binary Leavitt algebra from precisely `t₀s₀ = 1` with `s₀t₀ ≠ 1`.
-/

namespace GroupApproximation
namespace MFQuotientUnits

section Bridge

variable {R : Type*} [Ring R]

/-- A proper isometry makes `1` an infinite idempotent.

`t * s = 1` with `s * t ≠ 1` is the printed "one-sided inverse" configuration;
`1 = st + (1 - st)` is its decomposition. -/
theorem isInfiniteIdempotent_one_of_properIsometry {s t : R}
    (hts : t * s = 1) (hst : s * t ≠ 1) : IsInfiniteIdempotent R 1 := by
  have hst_idem : IsIdempotentElem (s * t) := by
    show s * t * (s * t) = s * t
    have e₁ : s * t * (s * t) = s * (t * s) * t := by noncomm_ring
    rw [e₁, hts, mul_one]
  refine ⟨s * t, 1 - s * t, hst_idem, ?_, ?_, ?_, ?_, ⟨t, s, hts.symm, rfl⟩, ?_⟩
  · show (1 - s * t) * (1 - s * t) = 1 - s * t
    have e₁ : (1 - s * t) * (1 - s * t) = 1 - s * t - s * t + s * t * (s * t) := by
      noncomm_ring
    rw [e₁, hst_idem]
    noncomm_ring
  · show s * t * (1 - s * t) = 0
    have e₁ : s * t * (1 - s * t) = s * t - s * t * (s * t) := by noncomm_ring
    rw [e₁, hst_idem, sub_self]
  · show (1 - s * t) * (s * t) = 0
    have e₁ : (1 - s * t) * (s * t) = s * t - s * t * (s * t) := by noncomm_ring
    rw [e₁, hst_idem, sub_self]
  · noncomm_ring
  · intro hzero
    apply hst
    have h₁ : s * t = 1 - (1 - s * t) := by noncomm_ring
    rw [h₁, hzero, sub_zero]

/-- The sandwich `x * a * y = 1` produces an idempotent in `aR` equivalent to
`1`, with the explicit pair `(a * y, x)`. -/
theorem isEquivalentIdempotent_one_of_sandwich {a x y : R} (hxay : x * a * y = 1) :
    IsIdempotentElem (a * (y * x)) ∧
      IsEquivalentIdempotent R (a * (y * x)) 1 := by
  constructor
  · show a * (y * x) * (a * (y * x)) = a * (y * x)
    have e₁ : a * (y * x) * (a * (y * x)) = a * y * (x * a * y) * x := by
      noncomm_ring
    rw [e₁, hxay, mul_one]
    noncomm_ring
  · refine ⟨a * y, x, by noncomm_ring, ?_⟩
    have e₁ : x * (a * y) = x * a * y := by noncomm_ring
    rw [e₁, hxay]

/-- **The bridge.**  A simple ring in which every nonzero element sandwiches to
`1`, and which carries one proper isometry, is purely infinite simple in the
printed idempotent form. -/
theorem isPurelyInfiniteSimpleRing_of_sandwich
    (hsimple : IsSimpleRing R) {s t : R} (hts : t * s = 1) (hst : s * t ≠ 1)
    (hsand : ∀ a : R, a ≠ 0 → ∃ x y : R, x * a * y = 1) :
    IsPurelyInfiniteSimpleRing R := by
  refine ⟨hsimple, ?_⟩
  intro a ha
  obtain ⟨x, y, hxay⟩ := hsand a ha
  obtain ⟨hidem, hequiv⟩ := isEquivalentIdempotent_one_of_sandwich hxay
  exact ⟨a * (y * x), y * x, rfl, hidem,
    IsInfiniteIdempotent.of_equivalent hidem hequiv
      (isInfiniteIdempotent_one_of_properIsometry hts hst)⟩

end Bridge

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms
  GroupApproximation.MFQuotientUnits.isInfiniteIdempotent_one_of_properIsometry
#audit_axioms
  GroupApproximation.MFQuotientUnits.isEquivalentIdempotent_one_of_sandwich
#audit_axioms
  GroupApproximation.MFQuotientUnits.isPurelyInfiniteSimpleRing_of_sandwich
