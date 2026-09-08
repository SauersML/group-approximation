import GroupApproximation.Algebra.PurelyInfiniteSandwich
import GroupApproximation.Algebra.CornerRing
import GroupApproximation.Manuscript.OneSidedMFRadical.MFHomKernel

/-!
# Every nonzero idempotent's corner sandwiches to its own unit

`Algebra/PurelyInfiniteSandwich.lean` proves that every nonzero element of a
purely infinite simple ring `R` sandwiches to `1`.  This module transports that
fact to the corner `Corner R e he` at any nonzero idempotent `e`, **without**
needing the corner to be independently purely infinite simple.

Ara--Goodearl--Pardo reach the corner's own comparison theory through their
Proposition 1.5 applied inside the corner; that route is not taken here.  The
corner's unit is `e`, and conjugating a global sandwich pair by `e` on both
sides lands it back inside the corner directly:

    `(e * x * e) * a * (e * y * e) = e * (x * a * y) * e = e * 1 * e = e`,

using `e * a = a = a * e` (the defining equations of the corner) to erase the
inner `e`s.  So the corner's own sandwich property is free once `R`'s is
proved, for every nonzero idempotent `e`, not just an infinite one.

## What this feeds

`AGPMenalMoncasiReduction` and `AGPStepOne` both need to place elements of the
corner-unit group inside `cornerUnitSubgroup R`, whose definition asks for a
countable ring `S`, a proper isometry pair `t * s = 1` in `S`, and the fullness
condition that `1 - s * t` generates `S` as a two-sided ideal.  Taking
`S := Corner R e he` for a suitably chosen idempotent `e`, this module supplies
the sandwich property that makes both the isometry pair and the fullness
witness constructible: a proper isometry pair `t, s` with `t * s = e ≠ s * t`
comes from `e` being infinite (`IsInfiniteIdempotent`, elsewhere in the
Ara--Goodearl--Pardo development), and fullness is then this lemma applied to
`a := e - s * t ≠ 0` inside the corner, a single sandwich rather than a
citation of corner simplicity.
-/

namespace GroupApproximation
namespace MFQuotientUnits

variable {R : Type*} [Ring R]

/-- **Corner sandwich.**  Every nonzero element of `Corner R e he` sandwiches to
the corner's own unit `e`, given only that `R` itself is purely infinite
simple — no fact about the corner beyond `e ≠ 0` is assumed. -/
theorem exists_corner_sandwich (hR : IsPurelyInfiniteSimpleRing R)
    {e : R} (he : IsIdempotentElem e) {a : Corner R e he} (ha : a ≠ 0) :
    ∃ s t : Corner R e he, t * a * s = 1 := by
  have hane : (a : R) ≠ 0 := fun h =>
    ha (corner_ext (h.trans (coe_corner_zero e he).symm))
  obtain ⟨x, y, hxy⟩ := exists_sandwich_of_isPurelyInfiniteSimpleRing hR hane
  have hae : e * (a : R) = (a : R) := a.2.1
  have hea : (a : R) * e = (a : R) := a.2.2
  have hmems : e * y * e ∈ cornerNonUnitalSubring e he := by
    constructor
    · show e * (e * y * e) = e * y * e
      have h1 : e * (e * y * e) = e * e * y * e := by noncomm_ring
      rw [h1, he]
    · show e * y * e * e = e * y * e
      have h1 : e * y * e * e = e * y * (e * e) := by noncomm_ring
      rw [h1, he]
  have hmemt : e * x * e ∈ cornerNonUnitalSubring e he := by
    constructor
    · show e * (e * x * e) = e * x * e
      have h1 : e * (e * x * e) = e * e * x * e := by noncomm_ring
      rw [h1, he]
    · show e * x * e * e = e * x * e
      have h1 : e * x * e * e = e * x * (e * e) := by noncomm_ring
      rw [h1, he]
  refine ⟨⟨e * y * e, hmems⟩, ⟨e * x * e, hmemt⟩, corner_ext ?_⟩
  show e * x * e * (a : R) * (e * y * e) = e
  calc e * x * e * (a : R) * (e * y * e)
      = e * (x * (e * (a : R) * e) * y) * e := by noncomm_ring
    _ = e * (x * (a : R) * y) * e := by rw [hae, hea]
    _ = e * 1 * e := by rw [hxy]
    _ = e := by rw [mul_one, he]

/-- **A fullness seed for `cornerUnitSubgroup`.**  From an infinite idempotent
`e` of `R`, produce a proper isometry pair inside the corner `Corner R e he`
together with a witness that the complementary idempotent generates the corner
as a two-sided ideal — the two ingredients `le_cornerUnitSubgroup` asks for.
Neither is a citation of Ara--Goodearl--Pardo Proposition 1.5: the isometry
pair is `exists_normalized_isometry` applied to `e`'s own infinite
decomposition, and fullness is `exists_corner_sandwich` applied to the
complementary idempotent, a single sandwich rather than corner simplicity. -/
theorem exists_cornerUnitSubgroup_seed [Countable R]
    (hR : IsPurelyInfiniteSimpleRing R) {e : R} (he : IsIdempotentElem e)
    (hinf : IsInfiniteIdempotent R e) :
    ∃ s t : Corner R e he, t * s = 1 ∧
      ∃ (m : ℕ) (a b : Fin m → Corner R e he),
        ∑ k, a k * (1 - s * t) * b k = 1 := by
  obtain ⟨f, g, hf, hg, hfg, hgf, hsum, hequiv, hgne⟩ := hinf
  have hef : e * f = f := by rw [hsum, add_mul, hf, hgf, add_zero]
  have hfe : f * e = f := by rw [hsum, mul_add, hf, hfg, add_zero]
  have hge : g * e = g := by rw [hsum, mul_add, hgf, hg, zero_add]
  have heg : e * g = g := by rw [hsum, add_mul, hfg, hg, zero_add]
  obtain ⟨s, t, hts, hst, hes, hse, het, hte⟩ :=
    exists_normalized_isometry he hf hef hfe hequiv
  have hgc : (1 : Corner R e he) - (⟨s, hes, hse⟩ : Corner R e he) * ⟨t, het, hte⟩
      = ⟨g, heg, hge⟩ := corner_ext (by
    show e - s * t = g
    rw [hst, hsum]
    abel)
  refine ⟨⟨s, hes, hse⟩, ⟨t, het, hte⟩, corner_ext hts, ?_⟩
  rw [hgc]
  have hgne' : (⟨g, heg, hge⟩ : Corner R e he) ≠ 0 := fun h =>
    hgne (by simpa using congrArg (fun z : Corner R e he ↦ (z : R)) h)
  obtain ⟨s', t', hst'⟩ := exists_corner_sandwich hR he hgne'
  exact ⟨1, fun _ => t', fun _ => s', by simpa using hst'⟩

/-- **The corner-unit membership `AGPMenalMoncasiReduction` and `AGPStepOne`
both need.**  Every image of an elementary group `EL_n(eRe)`, `n ≥ 2`, at an
infinite idempotent `e`, lies in `cornerUnitSubgroup R` — with no citation of
Ara--Goodearl--Pardo Proposition 1.5 or of corner simplicity. -/
theorem cornerElementaryRange_le_cornerUnitSubgroup {R : Type} [Ring R]
    [Countable R] (hR : IsPurelyInfiniteSimpleRing R) {e : R}
    (he : IsIdempotentElem e) (hinf : IsInfiniteIdempotent R e) {n : ℕ}
    (hn : 2 ≤ n) (φ : elementaryGroup (Fin n) (Corner R e he) →* Rˣ) :
    φ.range ≤ cornerUnitSubgroup R := by
  obtain ⟨s, t, hts, m, a, b, hfull⟩ := exists_cornerUnitSubgroup_seed hR he hinf
  exact le_cornerUnitSubgroup (Corner R e he) s t hts ⟨m, a, b, hfull⟩ n hn φ

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.exists_corner_sandwich
#audit_axioms GroupApproximation.MFQuotientUnits.exists_cornerUnitSubgroup_seed
#audit_axioms GroupApproximation.MFQuotientUnits.cornerElementaryRange_le_cornerUnitSubgroup
