import GroupApproximation.GGT.HullSCTheorem71GeneralBounded
import GroupApproximation.GGT.HullSCLemma44BoundedLeastAreaCanonical
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's Theorem 7.1 at every acylindrically hyperbolic group, over the least-area leaves

The general chain of `HullSCTheorem71General` and `HullSCTheorem71GeneralBounded`,
fed by the same two leaves as the torsion-free chain of
`HullSCLemma44BoundedLeastAreaCanonical`:

* `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement`, Osin's
  Lemma 4.4 at least-area diagrams;
* `RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement`, Osin's Lemma 5.1
  in the embedded form.

The simultaneous peripheral selection and Corollary 5.7 are closed.  The
`…_of_boundedTransfer` forms record the implication from
`BoundedRelativeLinearAreaTransferStatement`, a producer of the embedded bridge.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **The canonical quotient at every ambient group, from the least-area
leaves.** -/
theorem hullCanonicalQuotientStatementGeneral_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    HullCanonicalQuotientStatementGeneral.{0} :=
  hullCanonicalQuotientStatementGeneral_of_boundedLemma44_of_lemma49
    (simultaneousAuxiliaryPeripheralSelection_of_finiteYi_theorem316
      yiSuitableFiniteFamily_closed)
    (boundedHullLemma44CanonicalQuotientStatement_of_quasiGeodesicLeastArea
      (relativeGreendlingerQuasiGeodesicSpellingLeastAreaStatement_of_leastAreaGreendlinger
        hgreendlinger relativeDiscRealizationSpellingStatement
        relativeExteriorArcConversionAtWordRotatedStatement)
      hbridge)
    (hullLemma49KernelPowerStatement_of_leastAreaGreendlinger hgreendlinger)

/-- **Hull's Theorem 7.1 at one target, at every ambient group, from the
least-area leaves.** -/
theorem hullOneStepStatementGeneral_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    HullOneStepStatementGeneral.{0} :=
  hullOneStepStatementGeneral_of_canonicalQuotient
    (hullCanonicalQuotientStatementGeneral_of_leastAreaLeaves hgreendlinger hbridge)

/-- **Hull's Theorem 7.1 for every number of targets, at every ambient group, from
the least-area leaves.** -/
theorem hullTowerStatementGeneral_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    HullTowerStatementGeneral.{0} :=
  hullTowerStatementGeneral_of_oneStep
    (hullOneStepStatementGeneral_of_leastAreaLeaves hgreendlinger hbridge)

/-- **Hull's Theorem 7.1 in its published ball form, at every acylindrically
hyperbolic group, from the least-area leaves.** -/
theorem hullBallFormStatementGeneral_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    HullBallFormStatementGeneral.{0} :=
  hullBallFormStatementGeneral_of_tower
    (hullTowerStatementGeneral_of_leastAreaLeaves hgreendlinger hbridge)

/-- The ball form at every ambient group from the least-area Greendlinger waist and
the bounded linear-area transfer, through the embedded bridge it produces. -/
theorem hullBallFormStatementGeneral_of_leastAreaGreendlinger_of_boundedTransfer
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (htransfer : BoundedRelativeLinearAreaTransferStatement.{0, 0, 0}) :
    HullBallFormStatementGeneral.{0} :=
  hullBallFormStatementGeneral_of_leastAreaLeaves hgreendlinger
    (relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_boundedTransfer
      htransfer)

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.hullCanonicalQuotientStatementGeneral_of_leastAreaLeaves
#audit_axioms GroupApproximation.HullSC.hullOneStepStatementGeneral_of_leastAreaLeaves
#audit_axioms GroupApproximation.HullSC.hullTowerStatementGeneral_of_leastAreaLeaves
#audit_axioms GroupApproximation.HullSC.hullBallFormStatementGeneral_of_leastAreaLeaves
#audit_axioms GroupApproximation.HullSC.hullBallFormStatementGeneral_of_leastAreaGreendlinger_of_boundedTransfer
