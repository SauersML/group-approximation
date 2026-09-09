import GroupApproximation.Algebra.PurelyInfiniteCornerSandwich
import GroupApproximation.Algebra.PurelyInfiniteBridge
import GroupApproximation.PropertyTT.RingHypotheses
import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsStepOne
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingFullIdeal
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import GroupApproximation.Meta.AxiomGuard

/-!
# Ara--Goodearl--Pardo Proposition 1.5 and the corners it produces

`non_mf_groups_exist.tex`, inside the proof of `thm:mf-quotient-units`:

> Every nonzero idempotent `e` of `R` is
> infinite~\cite[Proposition~1.5]{AGP}, so `eRe` contains `s,t` with
> `ts = e ≠ st`, and `eRe` is simple, so `e - st` generates `eRe` as a
> two-sided ideal …

The first clause is `MFQuotientUnitsStepOne.isInfiniteIdempotent_of_ne_zero`,
already in the tree and consumed here rather than reproved.  This module adds
the rest of the sentence and the structural fact behind it:

* `exists_properIsometry_corner` --- the printed `s, t` with `ts = e ≠ st`,
  living *inside* `eRe`, where they read as a proper isometry pair for the
  corner's own unit;
* `isSimpleRing_corner` --- the printed "`eRe` is simple";
* `isPurelyInfiniteSimpleRing_corner` --- the corner of a purely infinite
  simple ring at **any** nonzero idempotent is again purely infinite simple.
  This is the statement `Algebra/PurelyInfiniteCornerSandwich.lean` explicitly
  declined to prove ("without needing the corner to be independently purely
  infinite simple"); having it makes the whole Ara--Goodearl--Pardo §1
  development available inside a corner, which is what an induction on the
  rank of an idempotent decomposition needs.

## Why no circularity

Corner simplicity does *not* go through corner pure infiniteness.  It is the
sandwich property `exists_corner_sandwich`, which needs only `e ≠ 0` and pure
infiniteness of the ambient `R`, fed to `HasSingleSandwichDivision.isSimpleRing`.
Pure infiniteness of the corner is then the bridge
`isPurelyInfiniteSimpleRing_of_sandwich`: simplicity, the same sandwich
property, and one proper isometry --- and the isometry is Proposition 1.5
applied to `e` in `R`, not in `eRe`.

## What this is weaker than

Nothing here needs `[Countable R]`; the printed proof carries countability for
the group-theoretic conclusion, not for the idempotent algebra.
-/

namespace GroupApproximation
namespace MFQuotientUnits

variable {R : Type*} [Ring R]

/-! ### The printed isometry pair inside `eRe` -/

/-- **The printed "`eRe` contains `s,t` with `ts = e ≠ st`".**

Read inside the corner, whose unit is `e`, this says exactly that `eRe` is not
directly finite: `t * s = 1` and `s * t ≠ 1`.  The witnesses are the normalised
form of the equivalence `e ~ f` supplied by an infinite decomposition
`e = f + g`, and `s * t = f ≠ e` precisely because `g ≠ 0`. -/
theorem exists_properIsometry_corner {e : R} (he : IsIdempotentElem e)
    (hinf : IsInfiniteIdempotent R e) :
    ∃ s t : Corner R e he, t * s = 1 ∧ s * t ≠ 1 := by
  obtain ⟨f, g, hf, hg, hfg, hgf, hsum, hequiv, hgne⟩ := hinf
  have hef : e * f = f := by rw [hsum, add_mul, hf, hgf, add_zero]
  have hfe : f * e = f := by rw [hsum, mul_add, hf, hfg, add_zero]
  obtain ⟨s, t, hts, hst, hes, hse, het, hte⟩ :=
    exists_normalized_isometry he hf hef hfe hequiv
  refine ⟨⟨s, hes, hse⟩, ⟨t, het, hte⟩, corner_ext hts, ?_⟩
  intro hcon
  apply hgne
  have hcoe : s * t = e := by
    have hval := congrArg (fun z : Corner R e he ↦ (z : R)) hcon
    simpa using hval
  have hfe' : f = e := by rw [← hst, hcoe]
  have h1 : f + 0 = f + g := by
    rw [add_zero, ← hsum]
    exact hfe'
  exact (add_left_cancel h1).symm

/-! ### The corner is simple -/

/-- **The printed "`eRe` is simple".**

Proved from the corner sandwich property, which needs only `e ≠ 0`; corner
pure infiniteness is *not* used, so the next theorem may use this one. -/
theorem isSimpleRing_corner (hR : IsPurelyInfiniteSimpleRing R) {e : R}
    (he : IsIdempotentElem e) (hne : e ≠ 0) : IsSimpleRing (Corner R e he) := by
  haveI : Nontrivial (Corner R e he) := corner_nontrivial e he hne
  refine HasSingleSandwichDivision.isSimpleRing ?_
  intro a ha
  obtain ⟨s, t, hsandwich⟩ := exists_corner_sandwich hR he ha
  exact ⟨t, s, hsandwich⟩

/-! ### The corner is purely infinite simple -/

/-- **Corners inherit pure infiniteness.**  For every nonzero idempotent `e` of
a purely infinite simple ring, `eRe` is again purely infinite simple.

Ara--Goodearl--Pardo obtain this inside their §1 comparison theory; the route
here is the bridge `isPurelyInfiniteSimpleRing_of_sandwich`, whose three inputs
are corner simplicity, the corner sandwich property, and one proper isometry in
the corner --- the last supplied by Proposition 1.5 applied to `e` in `R`. -/
theorem isPurelyInfiniteSimpleRing_corner (hR : IsPurelyInfiniteSimpleRing R)
    {e : R} (he : IsIdempotentElem e) (hne : e ≠ 0) :
    IsPurelyInfiniteSimpleRing (Corner R e he) := by
  have hinf : IsInfiniteIdempotent R e := isInfiniteIdempotent_of_ne_zero hR he hne
  obtain ⟨s, t, hts, hst⟩ := exists_properIsometry_corner he hinf
  refine isPurelyInfiniteSimpleRing_of_sandwich
    (isSimpleRing_corner hR he hne) hts hst ?_
  intro a ha
  obtain ⟨s', t', hsandwich⟩ := exists_corner_sandwich hR he ha
  exact ⟨t', s', hsandwich⟩

/-- **The printed "`e - st` generates `eRe` as a two-sided ideal", literally.**

Inside the corner the printed `e - st` is `1 - s * t`, and "generates `eRe`"
is the two-sided span being everything. -/
theorem span_one_sub_eq_top_corner (hR : IsPurelyInfiniteSimpleRing R) {e : R}
    (he : IsIdempotentElem e) (hne : e ≠ 0) {s t : Corner R e he}
    (hst : s * t ≠ 1) :
    TwoSidedIdeal.span {(1 : Corner R e he) - s * t} = ⊤ := by
  haveI : IsSimpleRing (Corner R e he) := isSimpleRing_corner hR he hne
  have hnz : (1 : Corner R e he) - s * t ≠ 0 :=
    sub_ne_zero_of_ne fun h ↦ hst h.symm
  have hmem : (1 : Corner R e he) - s * t ∈
      TwoSidedIdeal.span {(1 : Corner R e he) - s * t} :=
    TwoSidedIdeal.subset_span rfl
  exact (TwoSidedIdeal.one_mem_iff _).mp
    (IsSimpleRing.one_mem_of_ne_zero_mem _ hnz hmem)

/-! ### The printed sentence -/

/-- **Ara--Goodearl--Pardo Proposition 1.5 and its printed consequences, as a
closed proposition.**

`non_mf_groups_exist.tex`, proof of `thm:mf-quotient-units`:

> Every nonzero idempotent `e` of `R` is infinite \[AGP, Proposition 1.5\], so
> `eRe` contains `s,t` with `ts = e ≠ st`, and `eRe` is simple, so `e - st`
> generates `eRe` as a two-sided ideal.

The corner is stated as `Corner R e he`, whose unit is `e`, so the printed
`ts = e ≠ st` is `t * s = 1 ≠ s * t` and the printed `e - st` is `1 - s * t`.
The fullness clause is given twice: as the printed two-sided span, and in the
indexed-sum form `∑ a_k (1 - st) b_k = 1` that the tree's corner-unit machinery
consumes.  Pure infiniteness of the corner is included because the same
argument delivers it. -/
def AGPPropositionOneFive : Prop :=
  ∀ (R : Type) [Ring R], IsPurelyInfiniteSimpleRing R →
    ∀ (e : R) (he : IsIdempotentElem e), e ≠ 0 →
      IsInfiniteIdempotent R e ∧
        IsSimpleRing (Corner R e he) ∧
        IsPurelyInfiniteSimpleRing (Corner R e he) ∧
        ∃ s t : Corner R e he, t * s = 1 ∧ s * t ≠ 1 ∧
          TwoSidedIdeal.span {(1 : Corner R e he) - s * t} = ⊤ ∧
          ∃ (m : ℕ) (a b : Fin m → Corner R e he),
            ∑ k, a k * (1 - s * t) * b k = 1

/-- **The printed sentence, proved.**  No literature input remains: the
infiniteness clause is `isInfiniteIdempotent_of_ne_zero`, the corner clauses
are proved above, and the fullness witness is
`FullDefectRing.isSimpleRing_full_of_not_directlyFinite` applied in the
corner. -/
theorem agpPropositionOneFive : AGPPropositionOneFive := by
  intro R _ hR e he hne
  have hinf : IsInfiniteIdempotent R e := isInfiniteIdempotent_of_ne_zero hR he hne
  haveI hsimple : IsSimpleRing (Corner R e he) := isSimpleRing_corner hR he hne
  obtain ⟨s, t, hts, hst⟩ := exists_properIsometry_corner he hinf
  obtain ⟨-, m, a, b, hfull⟩ :=
    Manuscript.OneSidedMFRadical.FullDefectRing.isSimpleRing_full_of_not_directlyFinite
      hts hst
  exact ⟨hinf, hsimple, isPurelyInfiniteSimpleRing_corner hR he hne,
    s, t, hts, hst, span_one_sub_eq_top_corner hR he hne hst, m, a, b, hfull⟩

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.exists_properIsometry_corner
#audit_axioms GroupApproximation.MFQuotientUnits.isSimpleRing_corner
#audit_axioms GroupApproximation.MFQuotientUnits.isPurelyInfiniteSimpleRing_corner
#audit_axioms GroupApproximation.MFQuotientUnits.span_one_sub_eq_top_corner
#audit_closed_axioms GroupApproximation.MFQuotientUnits.agpPropositionOneFive
