import GroupApproximation.GGT.RelHypProp23FromHullStep
import GroupApproximation.GGT.HullSCBoundedImageEmbeddingLeastArea
import GroupApproximation.GGT.HullSCLemma44BoundedLeastAreaCanonical
import GroupApproximation.Meta.AxiomGuard

/-!
# Fournier--Facio Proposition 2.3 over the least-area leaves

The manuscript quotient field `Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement` on Osin's
Theorem 2.4 at Hull's published relator (`GGT.RelHyp.fournierFacioQuotientStatement_of_boundedLeaves`),
with its three geometric inputs read off the two leaves of Hull's Theorem 7.1:

* the least-area Greendlinger waist `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement`,
* Osin's Lemma 5.1 in the embedded form `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement`.

The bounded canonical Lemma 4.4 is `HullSC.boundedHullLemma44CanonicalQuotientStatement_of_quasiGeodesicLeastArea`,
the image form of Lemma 5.1 is `HullSC.boundedImageEmbeddingStatement_of_quasiGeodesicLeastArea`, and
Lemma 4.9 is `HullSC.hullLemma49KernelPowerStatement_of_leastAreaGreendlinger`.  No re-spelling input
and no family-form admission occurs: the original collection of the quotient is the un-coned joint
image (`GGT.cyclicPeripheralRemovalStatement`).
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

/-- **The manuscript quotient field over the least-area leaves of Hull's Theorem 7.1.** -/
theorem fournierFacioQuotientStatement_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement := by
  have hgeom : HullSC.RelativeGreendlingerQuasiGeodesicSpellingLeastAreaStatement.{0, 0} :=
    HullSC.relativeGreendlingerQuasiGeodesicSpellingLeastAreaStatement_of_leastAreaGreendlinger
      hgreendlinger HullSC.relativeDiscRealizationSpellingStatement
      HullSC.relativeExteriorArcConversionAtWordRotatedStatement
  exact fournierFacioQuotientStatement_of_boundedLeaves
    (HullSC.boundedHullLemma44CanonicalQuotientStatement_of_quasiGeodesicLeastArea hgeom hbridge)
    (HullSC.boundedImageEmbeddingStatement_of_quasiGeodesicLeastArea hgeom hbridge)
    (HullSC.hullLemma49KernelPowerStatement_of_leastAreaGreendlinger hgreendlinger)

end RelHyp
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.RelHyp.fournierFacioQuotientStatement_of_leastAreaLeaves
