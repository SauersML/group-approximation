import GroupApproximation.GGT.HullSCBoundedImageEmbedding
import GroupApproximation.GGT.HullSCLeastAreaGreendlingerTwins
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 5.1, image form, from the least-area certificate

`BoundedImageEmbeddingStatement` (`GGT/HullSCBoundedImageEmbedding.lean`) is what Osin's Theorem 2.4
reads of Lemma 5.1 at the joint collection of Hull's Corollary 7.4.  The embedded bridge asks for
certificates only at least-area diagrams with a quasi-geodesic spelling, which is exactly what the
least-area spelling statement `RelativeGreendlingerQuasiGeodesicSpellingLeastAreaStatement` gives, so
the image form follows from the least-area leaves with the certificate's own `eps`.
-/

namespace GroupApproximation
namespace HullSC

universe u w

/-- **The image form from the least-area certificate theorem and the embedded bridge.** -/
theorem boundedImageEmbeddingStatement_of_quasiGeodesicLeastArea
    (hgeom : RelativeGreendlingerQuasiGeodesicSpellingLeastAreaStatement.{u, w})
    (hbridge : RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{u, u, w}) :
    BoundedImageEmbeddingStatement.{u, w} := by
  intro G _ Lambda D hD mu hmu hmuUpper
  obtain ⟨eps0, rho0, hcert⟩ := hgeom D hD mu hmu (le_trans hmuUpper (by norm_num))
  refine ⟨eps0, rho0, ?_⟩
  intro eps rho W Q _ q hq heps hrho h20 hsc hker
  have hsc0 : RelWord.IsBoundedLemma44Input D W eps0 mu rho :=
    hsc.mono_parameters heps le_rfl le_rfl
  have h20' : 20 * (eps0 + 1) ≤ rho := by omega
  exact hbridge D hD eps0 rho mu W q hq hmu hmuUpper h20' hsc0 hker
    (fun R Z hZ => hcert rho hrho W R hsc0.toIsLemma44Input Z hZ)

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.boundedImageEmbeddingStatement_of_quasiGeodesicLeastArea
