import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf
import GroupApproximation.Meta.AxiomGuard

/-!
# Fournier-Facio's `G₀` as Hull's Corollary 7.4 common quotient, over the Greendlinger leaf

`non_mf_groups_exist.tex`, lines 2160–2170:

> Fournier-Facio constructs a finitely presented torsion-free group `G₀` with property (T), a
> subgroup `Γ ≤ G₀` with property (T), an element `t ∈ G₀` with `tΓt⁻¹ ≤ Γ`, and a subgroup
> `J ≤ G₀` isomorphic to a finitely presented infinite simple group, such that `[Γ, J] = 1` and
> `tJt⁻¹ ≤ Γ` [FFF, §2].  The group `G₀` is obtained there as a common quotient of two finitely
> generated acylindrically hyperbolic groups by Hull's theorem [Hull, Corollary 7.4], which allows
> the quotient to be chosen acylindrically hyperbolic; we take `G₀` to be such a quotient.

Census rows `8097c371f35d` (Fournier-Facio constructs `G₀`) and `dab2f2bfe084` (`G₀` as Hull's
Corollary 7.4 common quotient).

## Route

Every endpoint applies the matching `TorsionFreeGreendlingerLeaf.*_of_greendlinger` theorem.  Those
theorems already discharge the other walls with closed producers:
`HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed` (Osin's Lemma 5.1, embedded),
`KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed` (a torsion-free hyperbolic group with
property (T)) and `HydeLodha.finitelyPresentedInfiniteSimple_closed` (Hyde–Lodha's `Q₂`).  So the
single remaining binder is

  `hgreendlinger : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`,

Osin's Lemma 4.4 at least-area diagrams, the Greendlinger waist of Hull's Theorem 7.1 and hence of
Corollary 7.4.  `FournierFacioRows` bundles the five forms the two rows cite, and
`fournierFacioRows_of_greendlinger` is its reduction.

## The leaf is still open

There is no binder-free closer of the leaf.  The honest leaf endpoint is

  `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals`

in `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/Assembly.lean`, over the two open Statements
`GreendlingerLeaf.P07InnerPocket.PocketFourPieceOffStatement` and
`GreendlingerLeaf.P10RoseExtremalTrim.RoseExtremalJunctionStatement`.
`TorsionFreeClosed/FournierFacioClosed.lean` applies it, giving
`manuscriptSentence_hullCommonQuotient_of_residuals` and likewise
`manuscriptSentence_fournierFacioQuotient_of_residuals`,
`manuscriptSentence_fournierFacioParagraph_of_residuals`, `theoremC_configuration_of_residuals`,
`theoremC_literatureInputs_of_residuals` and `fournierFacioRows_of_residuals`.

## Manuscript status

Every theorem here takes `hgreendlinger`, so the two rows stay `partial` until both residual
Statements are proved.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeClosed

/-- **Hull's Corollary 7.4, in the form the Fournier-Facio paragraph uses** (lines 2165–2169), over
the Greendlinger leaf. -/
theorem manuscriptSentence_hullCommonQuotient_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TheoremC.HullCommonQuotientStatement :=
  TorsionFreeGreendlingerLeaf.hullCommonQuotient_of_greendlinger hgreendlinger

/-- **The small cancellation quotient of the Fournier-Facio construction** (lines 2160–2169), the
`smallCancellationQuotient` field of `TheoremC.LiteratureInputs`, over the Greendlinger leaf. -/
theorem manuscriptSentence_fournierFacioQuotient_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TheoremC.FournierFacioQuotientStatement :=
  TorsionFreeGreendlingerLeaf.fournierFacioQuotient_of_greendlinger hgreendlinger

/-- **The Fournier-Facio paragraph, as printed** (lines 2160–2165), over the Greendlinger leaf. -/
theorem manuscriptSentence_fournierFacioParagraph_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TorsionFreePrinted.FournierFacioParagraph :=
  TorsionFreeGreendlingerLeaf.fournierFacioParagraph_of_greendlinger hgreendlinger

/-- **The configuration of the Fournier-Facio paragraph** (lines 2160–2170): `G₀` taken as an
acylindrically hyperbolic common quotient, over the Greendlinger leaf. -/
theorem theoremC_configuration_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    Nonempty TheoremC.Configuration :=
  TorsionFreeGreendlingerLeaf.configuration_of_greendlinger hgreendlinger

/-- **The literature inputs of the Fournier-Facio paragraph**, `TheoremC.LiteratureInputs`, over
the Greendlinger leaf. -/
theorem theoremC_literatureInputs_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    TheoremC.LiteratureInputs :=
  TorsionFreeGreendlingerLeaf.literatureInputs_of_greendlinger hgreendlinger

/-- **The Fournier-Facio rows, bundled**: Hull's Corollary 7.4 common quotient, the Fournier-Facio
quotient, the printed paragraph, the configuration and the literature inputs (census rows
`8097c371f35d`, `dab2f2bfe084`). -/
def FournierFacioRows : Prop :=
  TheoremC.HullCommonQuotientStatement ∧
    TheoremC.FournierFacioQuotientStatement ∧
      TorsionFreePrinted.FournierFacioParagraph ∧
        Nonempty TheoremC.Configuration ∧
          TheoremC.LiteratureInputs

/-- **The Fournier-Facio rows over the Greendlinger leaf.** -/
theorem fournierFacioRows_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    FournierFacioRows :=
  And.intro (manuscriptSentence_hullCommonQuotient_of_greendlinger hgreendlinger)
    (And.intro (manuscriptSentence_fournierFacioQuotient_of_greendlinger hgreendlinger)
      (And.intro (manuscriptSentence_fournierFacioParagraph_of_greendlinger hgreendlinger)
        (And.intro (theoremC_configuration_of_greendlinger hgreendlinger)
          (theoremC_literatureInputs_of_greendlinger hgreendlinger))))

end TorsionFreeClosed
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_hullCommonQuotient_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_fournierFacioQuotient_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_fournierFacioParagraph_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.theoremC_configuration_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.theoremC_literatureInputs_of_greendlinger
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.fournierFacioRows_of_greendlinger
