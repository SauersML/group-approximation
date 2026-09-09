import GroupApproximation.GGT.OsinLemma71Printed
import GroupApproximation.Manuscript.NonMF.TorsionFreePrintedTheorem
import GroupApproximation.Manuscript.NonMF.TorsionFreeSectionCitations
import GroupApproximation.Meta.AxiomGuard

/-!
# `sec:torsion-free` after Osin's Lemma 7.1 is proved

`GGT/OsinLemma71Printed.lean` proves `TorsionFreePrinted.OsinLemma71Printed`, so
`nonempty_hullPrintedInputs_iff` says the two-field bundle `HullPrintedInputs`
carries nothing beyond its small-cancellation field.  This module spends that:
every endpoint of `sec:torsion-free` that was carried over `HullPrintedInputs`
is restated over `HullSmallCancellationPrinted` — `thm:hull` alone.

Each theorem below is the corresponding theorem of
`Manuscript/NonMF/TorsionFreePrintedTheorem.lean` or
`Manuscript/NonMF/TorsionFreeSectionCitations.lean` with `hHull` replaced by
`hullPrintedInputs_of_smallCancellation h`.  Nothing else changes: the
conclusions are the same printed propositions, at the same universes, and the
remaining hypotheses are the same ones those files already carry.  So the count
of literature inputs of the section drops by one everywhere at once.

## What the section still rests on

* `thm:torsion-free` — the Fournier-Facio paragraph (or, through
  `_of_citations`, the five citations of the printed construction of `G₀`
  together with Burger–Mozes) and `thm:hull`.
* `cor:relative-quotient` — those, plus `HullSC.HullOneStepStatement`, which is
  Hull's Theorem 7.1 as his construction produces it.  That is a trade rather
  than a removal, as `TorsionFreeSectionCitations` explains, and this module
  does not change it.
* `cor:regular-nonmf-algebra` — those, plus Dahmani–Guirardel–Osin's
  Theorem 2.35 and Gerasimova–Osin's Theorem 1.1.
* `lem:saturation` — `thm:hull` alone.

Osin's Lemma 7.1 appears in none of them any more.

`#audit_axioms` rather than `#audit_closed_axioms`: these are implications with
leading inputs, which the closed form rejects by design.  What the audit
establishes is that the reduction adds nothing — no `sorryAx` reaches any of
them, so every open obligation is one of the named arguments.
-/

namespace GroupApproximation
namespace GGT
namespace OsinPrinted

open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted
open GroupApproximation.Manuscript.NonMF.TheoremC

universe u

/-! ## `lem:saturation` -/

/-- **`lem:saturation` from Hull's Theorem 7.1 alone.**

`manuscriptSaturation` takes the whole printed bundle; its Osin field is now
`osinLemma71Printed`, so the saturation lemma of `sec:torsion-free` rests on one
citation. -/
theorem manuscriptSaturation_of_smallCancellation
    (h : HullSmallCancellationPrinted.{u}) : PrintedSaturation.{u} :=
  manuscriptSaturation (hullPrintedInputs_of_smallCancellation h)

#audit_axioms manuscriptSaturation_of_smallCancellation

/-! ## `thm:torsion-free` -/

/-- **`thm:torsion-free` from the Fournier-Facio paragraph and `thm:hull`.** -/
theorem manuscriptTorsionFreeTheorem_of_smallCancellation
    (hFFF : FournierFacioParagraph) (h : HullSmallCancellationPrinted.{0}) :
    PrintedTorsionFreeTheorem :=
  manuscriptTorsionFreeTheorem hFFF (hullPrintedInputs_of_smallCancellation h)

/-- **`thm:torsion-free` in the radical form**, from the same two. -/
theorem manuscriptTorsionFreeFullMFRadical_of_smallCancellation
    (hFFF : FournierFacioParagraph) (h : HullSmallCancellationPrinted.{0}) :
    PrintedTorsionFreeFullMFRadical :=
  manuscriptTorsionFreeFullMFRadicalFromParagraph hFFF
    (hullPrintedInputs_of_smallCancellation h)

/-- **`thm:torsion-free` over the printed citations**, with Osin's Lemma 7.1
removed from the list. -/
theorem manuscriptTorsionFreeTheorem_of_citations_of_smallCancellation
    (I : LiteratureInputs) (hW : FinitelyPresentedInfiniteSimpleStatement)
    (h : HullSmallCancellationPrinted.{0}) : PrintedTorsionFreeTheorem :=
  manuscriptTorsionFreeTheorem_of_citations I hW
    (hullPrintedInputs_of_smallCancellation h)

/-- **`thm:torsion-free` in the radical form over the printed citations**, with
Osin's Lemma 7.1 removed from the list. -/
theorem manuscriptTorsionFreeFullMFRadical_of_citations_of_smallCancellation
    (I : LiteratureInputs) (hW : FinitelyPresentedInfiniteSimpleStatement)
    (h : HullSmallCancellationPrinted.{0}) : PrintedTorsionFreeFullMFRadical :=
  manuscriptTorsionFreeFullMFRadical_of_citations I hW
    (hullPrintedInputs_of_smallCancellation h)

#audit_axioms manuscriptTorsionFreeTheorem_of_citations_of_smallCancellation

#audit_axioms manuscriptTorsionFreeFullMFRadical_of_citations_of_smallCancellation

/-! ## `cor:relative-quotient` and `cor:regular-nonmf-algebra` -/

/-- **`cor:relative-quotient` over the printed citations**, with Osin's
Lemma 7.1 removed from the list.  `hOne` stays: it is a different literature
statement from `thm:hull`, not a consequence of the two fields this module
collapses. -/
theorem manuscriptRelativeQuotient_of_citations_of_smallCancellation
    (I : LiteratureInputs) (hW : FinitelyPresentedInfiniteSimpleStatement)
    (h : HullSmallCancellationPrinted.{0})
    (hOne : HullSC.HullOneStepStatement.{0}) : PrintedRelativeQuotient :=
  manuscriptRelativeQuotient_of_citations I hW
    (hullPrintedInputs_of_smallCancellation h) hOne

/-- **`cor:regular-nonmf-algebra` over the printed citations**, with Osin's
Lemma 7.1 removed from the list.  The two C⋆-algebraic citations stay. -/
theorem manuscriptRegularNonMFAlgebra_of_citations_of_smallCancellation
    (I : LiteratureInputs) (hW : FinitelyPresentedInfiniteSimpleStatement)
    (h : HullSmallCancellationPrinted.{0}) (hDGO : DGOTheorem235Printed)
    (hGO : GerasimovaOsinTheorem11Printed) : PrintedRegularNonMFAlgebra :=
  manuscriptRegularNonMFAlgebra_of_citations I hW
    (hullPrintedInputs_of_smallCancellation h) hDGO hGO

#audit_axioms manuscriptRelativeQuotient_of_citations_of_smallCancellation

#audit_axioms manuscriptRegularNonMFAlgebra_of_citations_of_smallCancellation

end OsinPrinted
end GGT
end GroupApproximation
