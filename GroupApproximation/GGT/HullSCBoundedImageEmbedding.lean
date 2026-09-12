import GroupApproximation.GGT.HullSCLemma51EmbeddedBridge
import GroupApproximation.GGT.HullSCRelativeGreendlingerQuasiGeodesicSpelling
import GroupApproximation.GGT.HullSCLemma44BoundedInput
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 5.1 at a strongly bounded relator family, image form

`BoundedImageEmbeddingStatement` is what Osin's Theorem 2.4 reads of Lemma 5.1 at one hyperbolically
embedded collection: for every small `mu` there are thresholds such that the quotient by the normal
closure of a strongly bounded `C(eps, mu, rho)` family carries the image collection as a
hyperbolically embedded one.  It is read at the joint collection
`{H_λ} ∪ {⟨f₁⟩, ⟨f₂⟩, ⟨h₁⟩, ⟨h₂⟩}` of Hull's Corollary 7.4, on the re-spelling of the published
relator into joint letters.

`boundedImageEmbeddingStatement_of_quasiGeodesic` produces it from the certificate at quasi-geodesic
boundaries and the embedded bridge, with the certificate's own `eps`: every threshold is the
certificate's, and a larger `eps` only strengthens the input.
-/

namespace GroupApproximation
namespace HullSC

universe u w

/-- **Osin's Lemma 5.1, image form, over strongly bounded families.** -/
def BoundedImageEmbeddingStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : GGT.RelGenSet G Lambda),
    D.IsHyperbolicallyEmbedded →
      ∀ mu : ℝ, 0 < mu → mu ≤ 1 / 1000 →
        ∃ eps0 rho0 : ℕ,
          ∀ (eps rho : ℕ) (W : Set (List (GGT.RelLetter G Lambda)))
            {Q : Type u} [Group Q] (q : G →* Q) (hq : Function.Surjective q),
            eps0 ≤ eps → rho0 ≤ rho → 20 * (eps + 1) ≤ rho →
            RelWord.IsBoundedLemma44Input D W eps mu rho →
            q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
              (D.mapSurjective q hq).IsHyperbolicallyEmbedded

/-- **The image form from the certificate theorem and the embedded bridge.** -/
theorem boundedImageEmbeddingStatement_of_quasiGeodesic
    (hgeom : RelativeGreendlingerQuasiGeodesicSpellingStatement.{u, w})
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

#audit_axioms GroupApproximation.HullSC.boundedImageEmbeddingStatement_of_quasiGeodesic
