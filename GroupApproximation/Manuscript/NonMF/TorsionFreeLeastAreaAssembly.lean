import GroupApproximation.GGT.HullSCLemma44BoundedLeastAreaCanonical
import GroupApproximation.Manuscript.NonMF.TorsionFreeLeafAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# `sec:torsion-free` over the least-area leaves

`TorsionFreeLeafAssembly` runs the section over the historical Greendlinger waist
and Osin's Lemma 5.1 bridge in its landed control form.  Osin's own proof gives
Lemma 4.4 at least-area diagrams, and Lemma 5.1 is consumed only through
hyperbolic embeddedness of the image family, so the leaves the section rests on
are:

* `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement` — Osin's
  Lemma 4.4 at least-area diagrams;
* `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement` — Osin's
  Lemma 5.1 in the embedded form, proved directly from Osin's (18)–(21);
* `TorsionFreePrinted.FournierFacioParagraph` — the paragraph of tex lines
  1675–1685;
* `TorsionFreePrinted.SimpleUniqueTraceAtHypEmbedded` and
  `TorsionFreePrinted.GerasimovaOsinTheorem11Printed` — the two C⋆-algebraic
  inputs of `cor:regular-nonmf-algebra`.

The endpoints below take them as named hypotheses of intermediate lemmas and
become closed corollaries when their producers land.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeLeastAreaAssembly

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

/-- **`thm:hull` as printed, at a torsion-free ambient group**, from the
least-area Greendlinger waist and the embedded bridge. -/
theorem hullSmallCancellationTorsionFreePrinted_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    HullSmallCancellationTorsionFreePrinted.{0} :=
  hullSmallCancellationTorsionFreePrinted_of_oneStep
    (HullSC.hullOneStepStatement_of_leastAreaLeaves hgreendlinger hbridge)

/-- **`lem:saturation` as printed** (tex line 1650), from the same two leaves. -/
theorem printedSaturationNoOmega_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    PrintedSaturationNoOmega.{0} :=
  manuscriptSaturationNoOmega_of_torsionFreePrinted
    (hullSmallCancellationTorsionFreePrinted_of_leastAreaLeaves hgreendlinger hbridge)

/-- **`thm:torsion-free`, exactly as printed** (tex line 284), from the
Fournier-Facio paragraph and the two Hull leaves. -/
theorem manuscriptTorsionFreeTheorem_of_leastAreaLeaves (hFFF : FournierFacioParagraph)
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    PrintedTorsionFreeTheorem :=
  manuscriptTorsionFreeTheorem_of_torsionFreePrinted hFFF
    (hullSmallCancellationTorsionFreePrinted_of_leastAreaLeaves hgreendlinger hbridge)

/-- **`thm:torsion-free` in the radical form**, from the same three. -/
theorem manuscriptTorsionFreeFullMFRadical_of_leastAreaLeaves
    (hFFF : FournierFacioParagraph)
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    TheoremC.PrintedTorsionFreeFullMFRadical :=
  manuscriptTorsionFreeFullMFRadical_of_torsionFreePrinted hFFF
    (hullSmallCancellationTorsionFreePrinted_of_leastAreaLeaves hgreendlinger hbridge)

/-- **`cor:regular-nonmf-algebra`, along the printed proof**, from the
Fournier-Facio paragraph, the two Hull leaves, Dahmani–Guirardel–Osin's Theorem
2.35 at its source hypothesis, and Gerasimova–Osin's Theorem 1.1. -/
theorem manuscriptRegularNonMFAlgebra_of_leastAreaLeaves (hFFF : FournierFacioParagraph)
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hDGO : SimpleUniqueTraceAtHypEmbedded)
    (hGO : GerasimovaOsinTheorem11Printed) : PrintedRegularNonMFAlgebra :=
  TorsionFreeLeafAssembly.manuscriptRegularNonMFAlgebra_of_saturationNoOmega hFFF
    (printedSaturationNoOmega_of_leastAreaLeaves hgreendlinger hbridge) hDGO hGO

end TorsionFreeLeastAreaAssembly
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLeastAreaAssembly.hullSmallCancellationTorsionFreePrinted_of_leastAreaLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLeastAreaAssembly.printedSaturationNoOmega_of_leastAreaLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLeastAreaAssembly.manuscriptTorsionFreeTheorem_of_leastAreaLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLeastAreaAssembly.manuscriptTorsionFreeFullMFRadical_of_leastAreaLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLeastAreaAssembly.manuscriptRegularNonMFAlgebra_of_leastAreaLeaves
