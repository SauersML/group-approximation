import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:hull`, its hypotheses, conclusion and proof paragraph, over the Greendlinger leaf

`non_mf_groups_exist.tex`, lines 2122–2134:

> **Theorem (Hull's small cancellation theorem)** (`\label{thm:hull}`).  Let `G` be acylindrically
> hyperbolic, let `N ≤ G` be suitable with respect to `A`, and let `g₁, …, g_m ∈ G`.  Then there is
> a surjective homomorphism `φ : G → Q` such that `Q` is acylindrically hyperbolic,
> `φ(gᵢ) ∈ φ(N)` for all `i`, and every element of finite order in `Q` is the image of an element
> of the same order in `G`.
>
> Hull's proof treats `m = 1` by passing to `G/⟨⟨r⟩⟩_G` for one element `r` and the general case by
> induction on `m`, using his clause (d), that `φ(N)` is again suitable, so `ker φ` is the normal
> closure of `m` elements and `Q` is finitely presented when `G` is.

Census rows `8aead549f1fe` (hypotheses), `4895f03fdf5f` (conclusion), `bcc99703f838` (proof
paragraph).

## Route

Every endpoint applies the matching `TorsionFreeGreendlingerLeaf.*_of_greendlinger` theorem.  Those
theorems already discharge the other walls with closed producers
(`HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`), so the single remaining binder is

  `hgreendlinger : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`,

Osin's Lemma 4.4 at least-area diagrams (through Lemmas 9.4 and 9.7).  `HullTheoremRows` bundles the
five forms the three rows cite, and `hullTheoremRows_of_greendlinger` is its reduction.

The alphabet is not specialised: the leaf is taken at universes `.{0, 0, 0}` exactly as the
`TorsionFreeGreendlingerLeaf` endpoints consume it (cartography pitfall F2).

## Closer that a later landing plugs in

The leaf is closed, without binders and universe-polymorphically, by

  `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea`

in `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/Assembly.lean`.  That module is not imported
here: its `Piece01..Piece10` proofs have not landed.  Once it builds, the closed endpoints are

```
theorem manuscriptSentence_hullTheorem :
    TorsionFreeSectionSentences.PrintedHullSmallCancellationCurrent.{0} :=
  manuscriptSentence_hullTheorem_of_greendlinger
    GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}
```

and likewise for `_osin`, `_limitSet`, `manuscriptSentence_hullTorsionFree`,
`manuscriptSentence_hullProofParagraph` and `hullTheoremRows`, each audited with
`#audit_closed_axioms`.

## Manuscript status

Every theorem here takes `hgreendlinger`, so the three rows stay `partial` until the closer lands.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeClosed

/-- **`thm:hull` as printed**, at Hull's Cayley-graph notion of acylindrical hyperbolicity (lines
2122–2127), over the Greendlinger leaf. -/
theorem manuscriptSentence_hullTheorem_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeSectionSentences.PrintedHullSmallCancellationCurrent.{0} :=
  TorsionFreeGreendlingerLeaf.printedHullTheorem_of_greendlinger hgreendlinger

/-- **`thm:hull` at Osin's notion** (lines 2122–2127), over the Greendlinger leaf. -/
theorem manuscriptSentence_hullTheoremOsin_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeOsinNotion.PrintedHullSmallCancellationOsin :=
  TorsionFreeGreendlingerLeaf.printedHullTheoremOsin_of_greendlinger hgreendlinger

/-- **`thm:hull` at the limit-set notion** (lines 2122–2127), over the Greendlinger leaf. -/
theorem manuscriptSentence_hullTheoremLimitSet_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeLimitSetNotion.PrintedHullSmallCancellationLimitSet :=
  TorsionFreeGreendlingerLeaf.printedHullTheoremLimitSet_of_greendlinger hgreendlinger

/-- **`thm:hull` at a torsion-free ambient group**, the form the proof of `lem:saturation` applies
(lines 2122–2127 and 2151), over the Greendlinger leaf. -/
theorem manuscriptSentence_hullTorsionFree_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreePrinted.HullSmallCancellationTorsionFreePrinted.{0} :=
  TorsionFreeGreendlingerLeaf.hullSmallCancellationTorsionFreePrinted_of_greendlinger hgreendlinger

/-- **The paragraph after `thm:hull`, as printed** (lines 2129–2133): the `m = 1` step, the
induction on `m`, and finite presentability of `Q`, over the Greendlinger leaf. -/
theorem manuscriptSentence_hullProofParagraph_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreeSectionSentencesFourLeaves.PrintedHullProofParagraph :=
  TorsionFreeGreendlingerLeaf.printedHullProofParagraph_of_greendlinger hgreendlinger

/-- **The `thm:hull` rows, bundled**: the theorem at the three notions of acylindrical
hyperbolicity, its torsion-free form, and the proof paragraph (census rows `8aead549f1fe`,
`4895f03fdf5f`, `bcc99703f838`). -/
def HullTheoremRows : Prop :=
  TorsionFreeSectionSentences.PrintedHullSmallCancellationCurrent.{0} ∧
    TorsionFreeOsinNotion.PrintedHullSmallCancellationOsin ∧
      TorsionFreeLimitSetNotion.PrintedHullSmallCancellationLimitSet ∧
        TorsionFreePrinted.HullSmallCancellationTorsionFreePrinted.{0} ∧
          TorsionFreeSectionSentencesFourLeaves.PrintedHullProofParagraph

/-- **The `thm:hull` rows over the Greendlinger leaf.** -/
theorem hullTheoremRows_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    HullTheoremRows :=
  And.intro (manuscriptSentence_hullTheorem_of_greendlinger hgreendlinger)
    (And.intro (manuscriptSentence_hullTheoremOsin_of_greendlinger hgreendlinger)
      (And.intro (manuscriptSentence_hullTheoremLimitSet_of_greendlinger hgreendlinger)
        (And.intro (manuscriptSentence_hullTorsionFree_of_greendlinger hgreendlinger)
          (manuscriptSentence_hullProofParagraph_of_greendlinger hgreendlinger))))

end TorsionFreeClosed
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_hullTheorem_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_hullTheoremOsin_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_hullTheoremLimitSet_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_hullTorsionFree_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_hullProofParagraph_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.hullTheoremRows_of_greendlinger
