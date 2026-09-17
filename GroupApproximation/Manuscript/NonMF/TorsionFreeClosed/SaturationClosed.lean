import GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.SaturationLemma
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:saturation` and its two `thm:hull` proof steps, closed

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

Lane nm-torsionfree-02.  `TorsionFreeClosed/SaturationLemma.lean` proves each endpoint over the
single binder `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}` (Osin's
Lemma 4.4 at least-area diagrams; every other wall is discharged there by closed producers).  This
module discharges that binder with the universe-polymorphic, binder-free closer
`GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea`
(`GreendlingerLeaf/Assembly.lean`), instantiated at `.{0, 0, 0}`.  The alphabet is not
specialised: the closer is applied as the whole statement at those universes.

## Manuscript status

Every endpoint here has no inputs and is audited with `#audit_closed_axioms`.  They close the three
rows once `GreendlingerLeaf/Assembly.lean` (and so its piece proofs) builds.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeClosed

/-- **`lem:saturation` as printed** (lines 2134–2140), closed. -/
theorem manuscriptSentence_saturation : TorsionFreePrinted.PrintedSaturationNoOmega.{0} :=
  manuscriptSentence_saturation_of_greendlinger
    GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

/-- **`lem:saturation` at Osin's notion** (lines 2134–2140), closed. -/
theorem manuscriptSentence_saturation_osin : TorsionFreeOsinNotion.PrintedSaturationOsin :=
  manuscriptSentence_saturation_osin_of_greendlinger
    GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

/-- **`lem:saturation` at the limit-set notion** (lines 2134–2140), closed. -/
theorem manuscriptSentence_saturation_limitSet :
    TorsionFreeLimitSetNotion.PrintedSaturationLimitSet :=
  manuscriptSentence_saturation_limitSet_of_greendlinger
    GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

/-- **The pair `h₁, h₂` and `thm:hull` again** (lines 2146–2150, in the proof of
`lem:saturation`), closed. -/
theorem manuscriptSentence_saturationPairAndHullAgain :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationPairAndHullAgain :=
  manuscriptSentence_saturationPairAndHullAgain_of_greendlinger
    GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

/-- **"Apply Theorem `thm:hull` to `N₀`"** (lines 2150–2152, in the proof of `lem:saturation`),
closed. -/
theorem manuscriptSentence_saturationApplyHull :
    TorsionFreeSectionSentencesFourLeaves.PrintedSaturationApplyHull :=
  manuscriptSentence_saturationApplyHull_of_greendlinger
    GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

/-- **The `lem:saturation` rows, bundled and closed** (census rows `2f55113239ce`,
`2d1cd22e5f49`, `2f997e5af4e6`). -/
theorem saturationLemmaRows : SaturationLemmaRows :=
  saturationLemmaRows_of_greendlinger
    GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

end TorsionFreeClosed
end NonMF
end Manuscript
end GroupApproximation

#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_saturation
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_saturation_osin
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_saturation_limitSet
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_saturationPairAndHullAgain
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_saturationApplyHull
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.saturationLemmaRows
