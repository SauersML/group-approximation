import GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.SaturationLemma
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:saturation` and its two `thm:hull` proof steps, over the two open Greendlinger residuals

`non_mf_groups_exist.tex`, lines 2134–2158:

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

Lane nm-torsionfree-02; honesty repair gl-asm-14.  `TorsionFreeClosed/SaturationLemma.lean` proves
each endpoint over the single binder
`GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}` (Osin's Lemma 4.4 at
least-area diagrams; every other wall is discharged there by closed producers).  This module
discharges that binder with
`GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals`
(`GreendlingerLeaf/Assembly.lean`) at `.{0, 0, 0}`, so every endpoint takes the two open leaf
residuals

* `hoff : GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceOffStatement.{0, 0, 0}`;
* `hjunction : GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.RoseExtremalJunctionStatement.{0, 0, 0}`.

An earlier version stated these endpoints binder-free, citing a leaf closer
`GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea` that did not build (it cited the
missing names `Piece06.proof` and `Piece10.proof`).  The binder-free names are removed; nothing
imported them.

## Manuscript status

NOT closed.  Every endpoint takes `hoff` and `hjunction` and is audited with `#audit_axioms`.  The
three rows stay `partial` until both residual Statements are proved.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeClosed

/-- **`lem:saturation` as printed** (lines 2134–2140), over the two open Greendlinger residuals. -/
theorem manuscriptSentence_saturation_of_residuals
    (hoff : GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceOffStatement.{0, 0, 0})
    (hjunction :
      GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.RoseExtremalJunctionStatement.{0, 0, 0}) :
    TorsionFreePrinted.PrintedSaturationNoOmega.{0} :=
  manuscriptSentence_saturation_of_greendlinger
    (GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
      hoff hjunction)

/-- **`lem:saturation` at Osin's notion** (lines 2134–2140), over the two open Greendlinger
residuals. -/
theorem manuscriptSentence_saturation_osin_of_residuals
    (hoff : GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceOffStatement.{0, 0, 0})
    (hjunction :
      GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.RoseExtremalJunctionStatement.{0, 0, 0}) :
    TorsionFreeOsinNotion.PrintedSaturationOsin :=
  manuscriptSentence_saturation_osin_of_greendlinger
    (GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
      hoff hjunction)

/-- **`lem:saturation` at the limit-set notion** (lines 2134–2140), over the two open Greendlinger
residuals. -/
theorem manuscriptSentence_saturation_limitSet_of_residuals
    (hoff : GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceOffStatement.{0, 0, 0})
    (hjunction :
      GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.RoseExtremalJunctionStatement.{0, 0, 0}) :
    TorsionFreeLimitSetNotion.PrintedSaturationLimitSet :=
  manuscriptSentence_saturation_limitSet_of_greendlinger
    (GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
      hoff hjunction)

/-- **The pair `h₁, h₂` and `thm:hull` again** (lines 2146–2150, in the proof of
`lem:saturation`), over the two open Greendlinger residuals. -/
theorem manuscriptSentence_saturationPairAndHullAgain_of_residuals
    (hoff : GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceOffStatement.{0, 0, 0})
    (hjunction :
      GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.RoseExtremalJunctionStatement.{0, 0, 0}) :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationPairAndHullAgain :=
  manuscriptSentence_saturationPairAndHullAgain_of_greendlinger
    (GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
      hoff hjunction)

/-- **"Apply Theorem `thm:hull` to `N₀`"** (lines 2150–2152, in the proof of `lem:saturation`),
over the two open Greendlinger residuals. -/
theorem manuscriptSentence_saturationApplyHull_of_residuals
    (hoff : GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceOffStatement.{0, 0, 0})
    (hjunction :
      GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.RoseExtremalJunctionStatement.{0, 0, 0}) :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationApplyHull :=
  manuscriptSentence_saturationApplyHull_of_greendlinger
    (GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
      hoff hjunction)

/-- **The `lem:saturation` rows, bundled, over the two open Greendlinger residuals** (census rows
`2f55113239ce`, `2d1cd22e5f49`, `2f997e5af4e6`). -/
theorem saturationLemmaRows_of_residuals
    (hoff : GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceOffStatement.{0, 0, 0})
    (hjunction :
      GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.RoseExtremalJunctionStatement.{0, 0, 0}) :
    SaturationLemmaRows :=
  saturationLemmaRows_of_greendlinger
    (GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
      hoff hjunction)

end TorsionFreeClosed
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_saturation_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_saturation_osin_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_saturation_limitSet_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_saturationPairAndHullAgain_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_saturationApplyHull_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.saturationLemmaRows_of_residuals
