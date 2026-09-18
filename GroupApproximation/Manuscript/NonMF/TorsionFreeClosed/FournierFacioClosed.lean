import GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.FournierFacioQuotient
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Fournier-Facio's `G₀` as Hull's Corollary 7.4 common quotient, over the two open Greendlinger residuals

`non_mf_groups_exist.tex`, lines 2160–2170:

> Fournier-Facio constructs a finitely presented torsion-free group `G₀` with property (T), a
> subgroup `Γ ≤ G₀` with property (T), an element `t ∈ G₀` with `tΓt⁻¹ ≤ Γ`, and a subgroup
> `J ≤ G₀` isomorphic to a finitely presented infinite simple group, such that `[Γ, J] = 1` and
> `tJt⁻¹ ≤ Γ` [FFF, §2].  The group `G₀` is obtained there as a common quotient of two finitely
> generated acylindrically hyperbolic groups by Hull's theorem [Hull, Corollary 7.4], which allows
> the quotient to be chosen acylindrically hyperbolic; we take `G₀` to be such a quotient.

Census rows `8097c371f35d` (Fournier-Facio constructs `G₀`) and `dab2f2bfe084` (`G₀` as Hull's
Corollary 7.4 common quotient).  Lane nm-torsionfree-03; honesty repair gl-asm-14.

## Route

`TorsionFreeClosed.FournierFacioQuotient` proves each form over the single binder
`hgreendlinger : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`
(the other walls, Osin's Lemma 5.1 embedded, Kotowski–Ollivier and Hyde–Lodha's `Q₂`, are already
discharged there by closed producers).  Every endpoint here applies the matching `_of_greendlinger`
theorem to

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
two rows stay `partial` until both residual Statements are proved.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeClosed

/-- **Hull's Corollary 7.4, in the form the Fournier-Facio paragraph uses** (lines 2165–2169), over
the two open Greendlinger residuals. -/
theorem manuscriptSentence_hullCommonQuotient_of_residuals
    (hoff : GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceOffStatement.{0, 0, 0})
    (hjunction :
      GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.RoseExtremalJunctionStatement.{0, 0, 0}) :
    TheoremC.HullCommonQuotientStatement :=
  manuscriptSentence_hullCommonQuotient_of_greendlinger
    (GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
      hoff hjunction)

/-- **The small cancellation quotient of the Fournier-Facio construction** (lines 2160–2169), over
the two open Greendlinger residuals. -/
theorem manuscriptSentence_fournierFacioQuotient_of_residuals
    (hoff : GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceOffStatement.{0, 0, 0})
    (hjunction :
      GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.RoseExtremalJunctionStatement.{0, 0, 0}) :
    TheoremC.FournierFacioQuotientStatement :=
  manuscriptSentence_fournierFacioQuotient_of_greendlinger
    (GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
      hoff hjunction)

/-- **The Fournier-Facio paragraph, as printed** (lines 2160–2165), over the two open Greendlinger
residuals. -/
theorem manuscriptSentence_fournierFacioParagraph_of_residuals
    (hoff : GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceOffStatement.{0, 0, 0})
    (hjunction :
      GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.RoseExtremalJunctionStatement.{0, 0, 0}) :
    TorsionFreePrinted.FournierFacioParagraph :=
  manuscriptSentence_fournierFacioParagraph_of_greendlinger
    (GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
      hoff hjunction)

/-- **The configuration of the Fournier-Facio paragraph** (lines 2160–2170): `G₀` taken as an
acylindrically hyperbolic common quotient, over the two open Greendlinger residuals. -/
theorem theoremC_configuration_of_residuals
    (hoff : GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceOffStatement.{0, 0, 0})
    (hjunction :
      GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.RoseExtremalJunctionStatement.{0, 0, 0}) :
    Nonempty TheoremC.Configuration :=
  theoremC_configuration_of_greendlinger
    (GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
      hoff hjunction)

/-- **The literature inputs of the Fournier-Facio paragraph**, `TheoremC.LiteratureInputs`, over the
two open Greendlinger residuals. -/
theorem theoremC_literatureInputs_of_residuals
    (hoff : GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceOffStatement.{0, 0, 0})
    (hjunction :
      GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.RoseExtremalJunctionStatement.{0, 0, 0}) :
    TheoremC.LiteratureInputs :=
  theoremC_literatureInputs_of_greendlinger
    (GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
      hoff hjunction)

/-- **The Fournier-Facio rows, bundled, over the two open Greendlinger residuals** (census rows
`8097c371f35d`, `dab2f2bfe084`). -/
theorem fournierFacioRows_of_residuals
    (hoff : GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceOffStatement.{0, 0, 0})
    (hjunction :
      GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.RoseExtremalJunctionStatement.{0, 0, 0}) :
    FournierFacioRows :=
  fournierFacioRows_of_greendlinger
    (GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
      hoff hjunction)

end TorsionFreeClosed
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_hullCommonQuotient_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_fournierFacioQuotient_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.manuscriptSentence_fournierFacioParagraph_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.theoremC_configuration_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.theoremC_literatureInputs_of_residuals
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeClosed.fournierFacioRows_of_residuals
