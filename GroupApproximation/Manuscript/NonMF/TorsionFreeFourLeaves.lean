import GroupApproximation.Manuscript.NonMF.TorsionFreeSectionAssemblyClosedGO
import GroupApproximation.Manuscript.NonMF.TorsionFreeLimitSetEndpoints
import GroupApproximation.Manuscript.NonMF.TorsionFreeHullPrintedLeastArea
import GroupApproximation.GGT.OsinLimitSetSpelling
import GroupApproximation.Meta.AxiomGuard

/-!
# `sec:torsion-free` over exactly the four walls

The printed endpoints of `sec:torsion-free`, and `thm:torsion-free` itself, rest on four
statements that are not yet theorems:

* `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement`: Osin's Lemma 4.4
  at least-area diagrams, the Greendlinger waist of Hull's Theorem 7.1;
* `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement`: Osin's Lemma 5.1 in
  the embedded form;
* `TheoremC.KotowskiOllivierStatement`, that is `Hyperbolic.SharpExistence`: an infinite,
  finitely presented, torsion-free hyperbolic group with property (T);
* `TorsionFreePrinted.FinitelyPresentedInfiniteSimpleStatement`: a finitely presented,
  torsion-free, infinite simple group.

Each theorem below takes exactly the walls its proof uses, in this order, and nothing else.
Every other input of the printed proofs is already a theorem:

* Dahmani–Guirardel–Osin's Theorem 2.35,
  `TorsionFreeSectionAssembly.simpleUniqueTraceAtHypEmbedded_closed`;
* Gerasimova–Osin's Theorem 1.1, `TorsionFreePrinted.gerasimovaOsinTheorem11Printed`;
* Chiodo's universal group, `Higman.OmegaSharedProof.omegaInput`;
* Minasyan–Osin, through `GGT.Elementary.osinTheorem12_unconditional`;
* the free-product union geometry of Hull's Corollary 7.4;
* the hard direction of Osin's Theorem 1.1,
  `GGT.OsinClassification.isAcylindricallyHyperbolicOsin_of_limitSet`.

## Status

The wall producers still have open hypotheses:

* `GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_osinLemma97` needs Osin's
  Lemma 9.7 at one section;
* `HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_letterPullback` needs
  the quotient peripheral letter pullback;
* `KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_of_leaves` needs the zip, fold and
  fixed-clique leaves of `GHB(7)`;
* `HydeLodha.finitelyPresentedInfiniteSimpleStatement_of_leaves` needs Hyde–Lodha's
  Proposition 4.7 at `Q₂`.

Once a producer is a theorem, each endpoint that uses it becomes closed by applying the
matching theorem below.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeFourLeaves

/-! ## `thm:hull`, over the two Hull walls -/

/-- **`thm:hull` as printed, at every acylindrically hyperbolic group**, at Hull's
Cayley-graph notion.

> Let $G$ be acylindrically hyperbolic, let $N\le G$ be suitable with respect to $A$, and
> let $g_1,\dots,g_m\in G$.  Then there is a surjective homomorphism $\varphi\colon G\to Q$
> such that $Q$ is acylindrically hyperbolic, $\varphi(g_i)\in\varphi(N)$ for all $i$, and
> every element of finite order in $Q$ is the image of an element of the same order in $G$.

`non_mf_groups_exist.tex` line 1636, `\label{thm:hull}`. -/
theorem printedHullTheorem_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    TorsionFreeSectionSentences.PrintedHullSmallCancellationCurrent.{0} :=
  TorsionFreeHullPrintedLeastArea.manuscriptSentence_hullTheorem_of_leastAreaLeaves
    hgreendlinger hbridge

/-- **`thm:hull` at Osin's notion of acylindrical hyperbolicity** (line 1636,
`\label{thm:hull}`). -/
theorem printedHullTheoremOsin_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    TorsionFreeOsinNotion.PrintedHullSmallCancellationOsin :=
  TorsionFreeHullPrintedLeastArea.manuscriptSentence_hullTheoremOsin_of_leastAreaLeaves
    hgreendlinger hbridge

/-- **`thm:hull` at the limit-set notion of acylindrical hyperbolicity** (line 1636,
`\label{thm:hull}`). -/
theorem printedHullTheoremLimitSet_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    TorsionFreeLimitSetNotion.PrintedHullSmallCancellationLimitSet :=
  TorsionFreeLimitSetEndpoints.manuscriptHullTheoremLimitSet_of_leastAreaLeaves
    hgreendlinger hbridge

/-- **`thm:hull` at a torsion-free ambient group**, the form the proof of
`lem:saturation` applies (line 1665). -/
theorem hullSmallCancellationTorsionFreePrinted_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    TorsionFreePrinted.HullSmallCancellationTorsionFreePrinted.{0} :=
  TorsionFreeLeastAreaAssembly.hullSmallCancellationTorsionFreePrinted_of_leastAreaLeaves
    hgreendlinger hbridge

/-! ## `lem:saturation`, over the two Hull walls -/

/-- **`lem:saturation` as printed.**

> Let $G$ be finitely presented, torsion-free, and acylindrically hyperbolic, and let
> $N\trianglelefteq G$ be nontrivial.  Then there is a surjective homomorphism
> $\varphi\colon G\to Q$ such that $Q$ is two-generated, finitely presented, torsion-free,
> and acylindrically hyperbolic, and $\varphi(N)=Q$.

`non_mf_groups_exist.tex` line 1650, `\label{lem:saturation}`. -/
theorem printedSaturation_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    TorsionFreePrinted.PrintedSaturationNoOmega.{0} :=
  TorsionFreeLeastAreaAssembly.printedSaturationNoOmega_of_leastAreaLeaves hgreendlinger hbridge

/-- **`lem:saturation` at Osin's notion** (line 1650, `\label{lem:saturation}`). -/
theorem printedSaturationOsin_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    TorsionFreeOsinNotion.PrintedSaturationOsin :=
  TorsionFreeOsinNotion.manuscriptSaturationOsin_of_leastAreaLeaves hgreendlinger hbridge

/-- **`lem:saturation` at the limit-set notion** (line 1650, `\label{lem:saturation}`).
The hard direction of Osin's Theorem 1.1 is a theorem, so only the two Hull walls remain. -/
theorem printedSaturationLimitSet_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    TorsionFreeLimitSetNotion.PrintedSaturationLimitSet :=
  TorsionFreeLimitSetEndpoints.manuscriptSaturationLimitSet_of_leastAreaLeaves
    GGT.OsinClassification.isAcylindricallyHyperbolicOsin_of_limitSet hgreendlinger hbridge

/-! ## The Fournier-Facio paragraph -/

/-- **Hull's Corollary 7.4, in the form the Fournier-Facio paragraph uses.**

> The group $G_0$ is obtained there as a common quotient of two finitely generated
> acylindrically hyperbolic groups by Hull's theorem~\cite[Corollary~7.4]{Hull}, which
> allows the quotient to be chosen acylindrically hyperbolic; we take $G_0$ to be such a
> quotient.

`non_mf_groups_exist.tex` line 1680. -/
theorem hullCommonQuotient_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    TheoremC.HullCommonQuotientStatement :=
  HullSC.hullCommonQuotient_of_leastAreaLeaves hgreendlinger hbridge

/-- **The small cancellation quotient of the Fournier-Facio construction**, the
`smallCancellationQuotient` field of `TheoremC.LiteratureInputs`. -/
theorem fournierFacioQuotient_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    TheoremC.FournierFacioQuotientStatement :=
  GGT.RelHyp.fournierFacioQuotientStatement_of_leastAreaLeaves hgreendlinger hbridge

/-- **The literature inputs of the Fournier-Facio paragraph**, `TheoremC.LiteratureInputs`,
over the two Hull walls and the Kotowski-Ollivier wall.  Its Chiodo and Minasyan-Osin fields
are already theorems. -/
theorem literatureInputs_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : TheoremC.KotowskiOllivierStatement) : TheoremC.LiteratureInputs :=
  TorsionFreeLiteratureInputsLeastArea.literatureInputs_of_leastAreaLeaves hgreendlinger hbridge
    hKO

/-- **The configuration of the Fournier-Facio paragraph**, `TheoremC.Configuration`, with
its ambient group the acylindrically hyperbolic common quotient of Hull's Corollary 7.4
(line 1680). -/
theorem configuration_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : TheoremC.KotowskiOllivierStatement) : Nonempty TheoremC.Configuration :=
  TheoremC.exists_configuration (literatureInputs_of_fourLeaves hgreendlinger hbridge hKO)

/-- **The Fournier-Facio paragraph, as printed.**

> Fournier-Facio constructs a finitely presented torsion-free group $G_0$ with
> property (T), a subgroup $\Gamma\le G_0$ with property (T), an element $t\in G_0$ with
> $t\Gamma t^{-1}\le\Gamma$, and a subgroup $J\le G_0$ isomorphic to a finitely presented
> infinite simple group, such that $[\Gamma,J]=1$ and $tJt^{-1}\le\Gamma$.

`non_mf_groups_exist.tex` line 1675. -/
theorem fournierFacioParagraph_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : TheoremC.KotowskiOllivierStatement)
    (hW : TorsionFreePrinted.FinitelyPresentedInfiniteSimpleStatement) :
    TorsionFreePrinted.FournierFacioParagraph :=
  TorsionFreeLiteratureInputsLeastArea.fournierFacioParagraph_of_leastAreaLeaves hgreendlinger
    hbridge hKO hW

/-! ## `thm:torsion-free` -/

/-- **`thm:torsion-free`, exactly as printed.**

> There is a two-generated, finitely presented, torsion-free, acylindrically hyperbolic
> group $Q$ with property (T) such that every homomorphism from $Q$ to an MF group is
> trivial.  In particular, no nontrivial quotient of $Q$ is MF.

`non_mf_groups_exist.tex` line 284, `\label{thm:torsion-free}`. -/
theorem printedTorsionFreeTheorem_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : TheoremC.KotowskiOllivierStatement)
    (hW : TorsionFreePrinted.FinitelyPresentedInfiniteSimpleStatement) :
    TorsionFreePrinted.PrintedTorsionFreeTheorem :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheorem_of_hullLeaves hgreendlinger
    hbridge hKO hW

/-- **`thm:torsion-free` in the radical form** (line 284, `\label{thm:torsion-free}`). -/
theorem printedTorsionFreeFullMFRadical_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : TheoremC.KotowskiOllivierStatement)
    (hW : TorsionFreePrinted.FinitelyPresentedInfiniteSimpleStatement) :
    TheoremC.PrintedTorsionFreeFullMFRadical :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeFullMFRadical_of_hullLeaves
    hgreendlinger hbridge hKO hW

/-- **`thm:torsion-free` at Osin's notion** (line 284, `\label{thm:torsion-free}`). -/
theorem printedTorsionFreeTheoremOsin_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : TheoremC.KotowskiOllivierStatement)
    (hW : TorsionFreePrinted.FinitelyPresentedInfiniteSimpleStatement) :
    TorsionFreeOsinNotion.PrintedTorsionFreeTheoremOsin :=
  TorsionFreeLiteratureInputsLeastArea.manuscriptTorsionFreeTheoremOsin_of_hullLeaves
    hgreendlinger hbridge hKO hW

/-- **`thm:torsion-free` at the limit-set notion** (line 284, `\label{thm:torsion-free}`). -/
theorem printedTorsionFreeTheoremLimitSet_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : TheoremC.KotowskiOllivierStatement)
    (hW : TorsionFreePrinted.FinitelyPresentedInfiniteSimpleStatement) :
    TorsionFreeLimitSetNotion.PrintedTorsionFreeTheoremLimitSet :=
  TorsionFreeLimitSetEndpoints.manuscriptTorsionFreeTheoremLimitSet_of_hullLeaves hgreendlinger
    hbridge hKO hW

/-! ## `cor:regular-nonmf-algebra` -/

/-- **`cor:regular-nonmf-algebra`, along the printed proof.**

> The algebra $C^*_{\mathrm r}(Q)$ is separable, unital, simple, and generated by two
> unitaries.  It has a unique tracial state and stable rank one, and it is stably finite
> but not MF.

`non_mf_groups_exist.tex` line 1718, `\label{cor:regular-nonmf-algebra}`. -/
theorem printedRegularNonMFAlgebra_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : TheoremC.KotowskiOllivierStatement)
    (hW : TorsionFreePrinted.FinitelyPresentedInfiniteSimpleStatement) :
    TorsionFreePrinted.PrintedRegularNonMFAlgebra :=
  TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebra_of_hullLeaves_closedGO hgreendlinger
    hbridge hKO hW

/-- **`cor:regular-nonmf-algebra` at Osin's notion** (line 1718,
`\label{cor:regular-nonmf-algebra}`). -/
theorem printedRegularNonMFAlgebraOsin_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : TheoremC.KotowskiOllivierStatement)
    (hW : TorsionFreePrinted.FinitelyPresentedInfiniteSimpleStatement) :
    TorsionFreeOsinNotion.PrintedRegularNonMFAlgebraOsin :=
  TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebraOsin_of_hullLeaves_closedGO
    hgreendlinger hbridge hKO hW

/-- **`cor:regular-nonmf-algebra` at the limit-set notion** (line 1718,
`\label{cor:regular-nonmf-algebra}`). -/
theorem printedRegularNonMFAlgebraLimitSet_of_fourLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0})
    (hKO : TheoremC.KotowskiOllivierStatement)
    (hW : TorsionFreePrinted.FinitelyPresentedInfiniteSimpleStatement) :
    TorsionFreeLimitSetNotion.PrintedRegularNonMFAlgebraLimitSet :=
  TorsionFreeSectionAssembly.manuscriptRegularNonMFAlgebraLimitSet_of_hullLeaves_closedGO
    hgreendlinger hbridge hKO hW

end TorsionFreeFourLeaves
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeFourLeaves.printedHullTheorem_of_fourLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeFourLeaves.printedHullTheoremOsin_of_fourLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeFourLeaves.printedHullTheoremLimitSet_of_fourLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeFourLeaves.hullSmallCancellationTorsionFreePrinted_of_fourLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeFourLeaves.printedSaturation_of_fourLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeFourLeaves.printedSaturationOsin_of_fourLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeFourLeaves.printedSaturationLimitSet_of_fourLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeFourLeaves.hullCommonQuotient_of_fourLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeFourLeaves.fournierFacioQuotient_of_fourLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeFourLeaves.literatureInputs_of_fourLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeFourLeaves.configuration_of_fourLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeFourLeaves.fournierFacioParagraph_of_fourLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeFourLeaves.printedTorsionFreeTheorem_of_fourLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeFourLeaves.printedTorsionFreeFullMFRadical_of_fourLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeFourLeaves.printedTorsionFreeTheoremOsin_of_fourLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeFourLeaves.printedTorsionFreeTheoremLimitSet_of_fourLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeFourLeaves.printedRegularNonMFAlgebra_of_fourLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeFourLeaves.printedRegularNonMFAlgebraOsin_of_fourLeaves
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeFourLeaves.printedRegularNonMFAlgebraLimitSet_of_fourLeaves
