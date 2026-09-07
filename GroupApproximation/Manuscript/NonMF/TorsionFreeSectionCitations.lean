import GroupApproximation.GGT.HullSCCommonQuotientPrinted
import GroupApproximation.Manuscript.NonMF.FournierFacioParagraphFromSimpleFactor
import GroupApproximation.Manuscript.NonMF.RegularNonMFAlgebra
import GroupApproximation.Meta.AxiomGuard

/-!
# What `sec:torsion-free` rests on, after both reductions

`non_mf_groups_exist.tex`, section `sec:torsion-free`.  Its four printed
statements — `thm:torsion-free`, `cor:relative-quotient`,
`cor:regular-nonmf-algebra` and `lem:saturation` — were each carried over
`FournierFacioParagraph` (Fournier-Facio §2), `HullPrintedInputs` (Hull's
Theorem 7.1 with Osin's Lemma 7.1), `HullCommonQuotientPrinted` (Hull's
Corollary 7.4) and, for the algebra, two C⋆-algebraic citations.

Two of those are no longer citations:

* `HullSC.hullCommonQuotientPrinted_of_oneStep` proves Hull's Corollary 7.4 from
  his Theorem 7.1 for one relator;
* `TorsionFreePrinted.fournierFacioParagraph_of_literatureInputs` proves the
  Fournier-Facio paragraph from the construction the manuscript itself printed
  until the current draft, together with Burger–Mozes.

This module composes the two, so that each printed statement of the section has
one declaration naming **every** literature input it still rests on, with no
`FournierFacioParagraph` and no `HullCommonQuotientPrinted` among them.

## The inputs that remain, and what each costs

`TheoremC.LiteratureInputs` has five fields, and this repository's own
`TheoremCAssembly` supplies four of them:

| field | state on `origin/main` |
| --- | --- |
| `chiodo` | **proved**, `TheoremC.chiodo`, from Higman's ω-closure |
| `kotowskiOllivier` | **open** — the density model at a parameter in `(1/3,1/2)` |
| `smallCancellationQuotient` | **proved**, from Hull's one-step small cancellation over the free product |
| `minasyanOsin` | **proved**, down to Osin's Theorem 1.2, which is unconditional here |
| `hullCommonQuotient` | **proved**, down to Hull's Theorem 7.1 for one relator |

`FinitelyPresentedInfiniteSimpleStatement` is Burger–Mozes and is new.
`HullPrintedInputs` is Hull's Theorem 7.1 and Osin's Lemma 7.1.
`HullOneStepStatement` is Hull's Theorem 7.1 in the one-relator construction
form.  `DGOTheorem235Printed` and `GerasimovaOsinTheorem11Printed` are the two
C⋆-algebraic citations of `cor:regular-nonmf-algebra`.

## Hull's Theorem 7.1 appears twice, and that is not yet avoidable

`manuscriptRelativeQuotient_of_citations` takes both `HullPrintedInputs` and
`HullOneStepStatement`.  Both are Hull's Theorem 7.1, in two readings, and one
does not imply the other in the direction that would let them be merged here:

* `HullOneStepStatement` **does** supply
  `HullCorrectedInputs.HullInputsCorrected.smallCancellation`, through
  `HullSC.hullBallFormNG_of_oneStep` and
  `HullCorrectedInputs.smallCancellation_of_ballFormNG`;
* it does **not** supply `HullSmallCancellationPrinted`, the field of
  `HullPrintedInputs`, because that statement carries no `IsPowerTorsionFree G`
  hypothesis and every form of the one-step theorem does.  The header of
  `Manuscript/NonMF/HullPrintedInputs.lean` records the same asymmetry.

So the section could be run off `HullOneStepStatement` together with
`OsinLemma71Printed` alone — the two together give
`HullInputsCorrected`, which is what `Saturation.saturation` actually consumes —
but only after `TorsionFreePrinted.exists_saturatedQuotient` and the four
statements below are restated over `HullInputsCorrected` instead of
`HullPrintedInputs`.  That is a change to landed statements, so it is not made
here, and nothing in this module pretends it has been: the extra hypothesis is
visible in the type of `manuscriptRelativeQuotient_of_citations`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TheoremC

/-! ## `thm:torsion-free` -/

/-- **`thm:torsion-free`, over every literature input it still has.**

> There is a two-generated, finitely presented, torsion-free, acylindrically
> hyperbolic group `Q` with property (T) such that every homomorphism from `Q`
> to an MF group is trivial.  In particular, no nontrivial quotient of `Q` is
> MF.

Three hypotheses: the five citations of the earlier printed construction of
`G₀`, Burger–Mozes, and Hull's Theorem 7.1 with Osin's Lemma 7.1.  The printed
citation of Fournier-Facio §2 is gone. -/
theorem manuscriptTorsionFreeTheorem_of_citations (I : LiteratureInputs)
    (hW : FinitelyPresentedInfiniteSimpleStatement)
    (hHull : HullPrintedInputs.{0}) : PrintedTorsionFreeTheorem :=
  manuscriptTorsionFreeTheorem (fournierFacioParagraph_of_literatureInputs I hW)
    hHull

/-- **`thm:torsion-free` in the radical form**, over the same three
hypotheses. -/
theorem manuscriptTorsionFreeFullMFRadical_of_citations (I : LiteratureInputs)
    (hW : FinitelyPresentedInfiniteSimpleStatement)
    (hHull : HullPrintedInputs.{0}) : PrintedTorsionFreeFullMFRadical :=
  manuscriptTorsionFreeFullMFRadicalFromParagraph
    (fournierFacioParagraph_of_literatureInputs I hW) hHull

/-! ## `cor:relative-quotient` -/

/-- **`cor:relative-quotient`, over every literature input it still has.**

> Let `G` be finitely presented, torsion-free, and acylindrically hyperbolic,
> and let `Ω ⊆ G` be finite.  Then `G` has a two-generated, finitely presented,
> torsion-free, acylindrically hyperbolic quotient `P` with property (T) such
> that the quotient map is injective on `Ω` and every homomorphism from `P` to
> an MF group is trivial.

Neither of the corollary's two printed citations — Fournier-Facio §2 and Hull's
Corollary 7.4 — appears.  `hOne` is Hull's Theorem 7.1 for one relator, which
`hullCommonQuotientPrinted_of_oneStep` turns into Corollary 7.4; see the module
header for why it cannot be merged with `hHull`. -/
theorem manuscriptRelativeQuotient_of_citations (I : LiteratureInputs)
    (hW : FinitelyPresentedInfiniteSimpleStatement)
    (hHull : HullPrintedInputs.{0}) (hOne : HullSC.HullOneStepStatement.{0}) :
    PrintedRelativeQuotient :=
  HullSC.manuscriptRelativeQuotient_of_oneStep
    (fournierFacioParagraph_of_literatureInputs I hW) hHull hOne

/-! ## `cor:regular-nonmf-algebra` -/

/-- **`cor:regular-nonmf-algebra`, over every literature input it still has.**

> The algebra `C*_r(Q)` is separable, unital, generated by two unitaries,
> simple, has a unique tracial state, has stable rank one, is stably finite, and
> is not MF.

The two C⋆-algebraic citations stay: Dahmani–Guirardel–Osin's Theorem 2.35 and
Gerasimova–Osin's Theorem 1.1.  Osin's Theorem 1.2 — *"it contains a
non-degenerate hyperbolically embedded subgroup"* — is not among them, because
the printed proof uses that clause only to reach the hypothesis of
Dahmani–Guirardel–Osin, which `DGOTheorem235Printed` states directly. -/
theorem manuscriptRegularNonMFAlgebra_of_citations (I : LiteratureInputs)
    (hW : FinitelyPresentedInfiniteSimpleStatement)
    (hHull : HullPrintedInputs.{0}) (hDGO : DGOTheorem235Printed)
    (hGO : GerasimovaOsinTheorem11Printed) : PrintedRegularNonMFAlgebra :=
  manuscriptRegularNonMFAlgebra (fournierFacioParagraph_of_literatureInputs I hW)
    hHull hDGO hGO

/-! ## The axioms

All four take their literature inputs as hypotheses, so `#audit_closed_axioms`
does not apply.  What `#audit_axioms` establishes is that the composition adds
nothing: no `sorryAx` reaches any of them, so every open obligation of
`sec:torsion-free` is one of the named arguments above.  In particular the five
admissions of `Manuscript/NonMF/TheoremCAssembly.lean` are **not** among them —
they enter only when `TheoremC.literatureInputs` is supplied for `I`. -/

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.manuscriptTorsionFreeTheorem_of_citations

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.manuscriptTorsionFreeFullMFRadical_of_citations

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.manuscriptRelativeQuotient_of_citations

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.manuscriptRegularNonMFAlgebra_of_citations

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation
