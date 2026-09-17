import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:saturation` and the two proof steps that use `thm:hull`, over the Greendlinger leaf

`non_mf_groups_exist.tex`, lines 2136–2158:

> **Lemma (saturation)** (`\label{lem:saturation}`).  Let `G` be finitely presented, torsion-free,
> and acylindrically hyperbolic, and let `N ⊴ G` be nontrivial.  Then there is a surjective
> homomorphism `φ : G → Q` such that `Q` is two-generated, finitely presented, torsion-free, and
> acylindrically hyperbolic, and `φ(N) = Q`.
>
> *Proof (excerpt).*  By Hull [Corollary 5.7 and Lemma 5.8], `N` contains two elements `h₁, h₂`
> such that `N₀ = ⟨h₁, h₂⟩` is suitable with respect to a generating set `A' ⊇ A` to which Hull's
> small cancellation theorem again applies.  Apply Theorem `thm:hull` to `N₀`, with respect to
> `A'`, with `g₁, …, g_m` a finite generating set of `G`.

Census rows `2f55113239ce` (statement), `2d1cd22e5f49` (the 5.7/5.8 pair and "Hull again
applies"), `2f997e5af4e6` ("apply `thm:hull` to `N₀`").

## Route

Every endpoint applies the matching `TorsionFreeGreendlingerLeaf.*_of_greendlinger` theorem, whose
other walls are already discharged by closed producers.  The pair half of row `2d1cd22e5f49` is
unconditional already (`HullCitationSentences.printedSaturationHullPair`); only the "Hull's theorem
again applies" half carries the leaf.  The single remaining binder is

  `hgreendlinger : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`,

Osin's Lemma 4.4 at least-area diagrams.  `SaturationLemmaRows` bundles the five forms the three
rows cite, and `saturationLemmaRows_of_greendlinger` is its reduction.

## Closer that a later landing plugs in

The leaf is closed, without binders and universe-polymorphically, by

  `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea`

in `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/Assembly.lean`, not imported here because its
`Piece01..Piece10` proofs have not landed.  Once it builds, the closed endpoints are

```
theorem manuscriptSentence_saturation : TorsionFreePrinted.PrintedSaturationNoOmega.{0} :=
  manuscriptSentence_saturation_of_greendlinger
    GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}
```

and likewise for `_osin`, `_limitSet`, `manuscriptSentence_saturationPairAndHullAgain`,
`manuscriptSentence_saturationApplyHull` and `saturationLemmaRows`, each audited with
`#audit_closed_axioms`.

## Manuscript status

Every theorem here takes `hgreendlinger`, so the three rows stay `partial` until the closer lands.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeClosed

/-- **`lem:saturation` as printed** (lines 2136–2141), over the Greendlinger leaf. -/
theorem manuscriptSentence_saturation_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreePrinted.PrintedSaturationNoOmega.{0} :=
  TorsionFreeGreendlingerLeaf.printedSaturation_of_greendlinger hgreendlinger

/-- **`lem:saturation` at Osin's notion** (lines 2136–2141), over the Greendlinger leaf. -/
theorem manuscriptSentence_saturation_osin_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeOsinNotion.PrintedSaturationOsin :=
  TorsionFreeGreendlingerLeaf.printedSaturationOsin_of_greendlinger hgreendlinger

/-- **`lem:saturation` at the limit-set notion** (lines 2136–2141), over the Greendlinger leaf. -/
theorem manuscriptSentence_saturation_limitSet_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeLimitSetNotion.PrintedSaturationLimitSet :=
  TorsionFreeGreendlingerLeaf.printedSaturationLimitSet_of_greendlinger hgreendlinger

/-- **The pair `h₁, h₂` and `thm:hull` again** (lines 2148–2151, in the proof of
`lem:saturation`), over the Greendlinger leaf. -/
theorem manuscriptSentence_saturationPairAndHullAgain_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationPairAndHullAgain :=
  TorsionFreeGreendlingerLeaf.printedSaturationPairAndHullAgain_of_greendlinger hgreendlinger

/-- **"Apply Theorem `thm:hull` to `N₀`"** (lines 2151–2153, in the proof of `lem:saturation`),
over the Greendlinger leaf. -/
theorem manuscriptSentence_saturationApplyHull_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationApplyHull :=
  TorsionFreeGreendlingerLeaf.printedSaturationApplyHull_of_greendlinger hgreendlinger

/-- **The `lem:saturation` rows, bundled**: the lemma at the three notions of acylindrical
hyperbolicity and the two proof steps that invoke `thm:hull` (census rows `2f55113239ce`,
`2d1cd22e5f49`, `2f997e5af4e6`). -/
def SaturationLemmaRows : Prop :=
  TorsionFreePrinted.PrintedSaturationNoOmega.{0} ∧
    TorsionFreeOsinNotion.PrintedSaturationOsin ∧
      TorsionFreeLimitSetNotion.PrintedSaturationLimitSet ∧
        TorsionFreeSectionSentencesFourLeaves.PrintedSaturationPairAndHullAgain ∧
          TorsionFreeSectionSentencesFourLeaves.PrintedSaturationApplyHull

/-- **The `lem:saturation` rows over the Greendlinger leaf.** -/
theorem saturationLemmaRows_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    SaturationLemmaRows :=
  And.intro (manuscriptSentence_saturation_of_greendlinger hgreendlinger)
    (And.intro (manuscriptSentence_saturation_osin_of_greendlinger hgreendlinger)
      (And.intro (manuscriptSentence_saturation_limitSet_of_greendlinger hgreendlinger)
        (And.intro (manuscriptSentence_saturationPairAndHullAgain_of_greendlinger hgreendlinger)
          (manuscriptSentence_saturationApplyHull_of_greendlinger hgreendlinger))))

end TorsionFreeClosed
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_saturation_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_saturation_osin_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_saturation_limitSet_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_saturationPairAndHullAgain_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_saturationApplyHull_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.saturationLemmaRows_of_greendlinger
