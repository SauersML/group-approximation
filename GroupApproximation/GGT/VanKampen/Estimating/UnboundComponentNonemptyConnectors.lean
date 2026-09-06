import GroupApproximation.GGT.VanKampen.Estimating.UnboundComponentWordPolygons
import GroupApproximation.GGT.VanKampen.Estimating.UnboundNonemptyConnectors

/-!
# Uniform production of nonempty connectors in the dense component

The same epsilon and rho threshold as the completed metric polygon argument
produce actual nonempty words, even when a matched pair of ambient vertices
coincides. The strict bounds and shortening are available on those words.
No new scale choice or nonvanishing assumption is added to the polygon input.
-/

namespace GroupApproximation.GGT.VanKampen.UnboundEstimate

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
universe u w

def UnboundComponentNonemptyConnectorsStatement : Prop :=
  ∀ (G : Type u) [Group G] (Lambda : Type w) (D : RelGenSet G Lambda),
    (∀ x ∈ D.base, x⁻¹ ∈ D.base) →
    ∀ (delta lambda c mu : ℝ),
    IsHyperbolicSpace delta (Cayley D.alphabet) → 0 ≤ delta →
    0 < lambda → 0 ≤ c → 0 < mu →
    ∃ kappa : ℝ, 0 ≤ kappa ∧ ∃ eps rho0 : ℕ, 0 < rho0 ∧
      ∀ rho : ℕ, rho0 ≤ rho →
        OsinUnboundScale lambda c mu kappa (12 * ((delta + 6) + 1))
          (100000 * ((delta + 6) + 1)) eps rho ∧
        ∀ (n d : ℕ), 0 < n →
          ∀ (arcCount sideCount : Fin d → ℕ) (v : Fin d → ℕ → G)
            (word : Fin d → ℕ → List (RelLetter G Lambda)) (A B : Fin d → Set ℕ),
            (∑ k : Fin d, arcCount k) ≤ 53 * n →
            (∀ k, sideCount k ≤ 4 * arcCount k) →
            (∀ k, v k (sideCount k) = v k 0) →
            (∀ k i, i < sideCount k → v k (i + 1) = v k i * RelLetter.listVal (word k i)) →
            (∀ k i, i < sideCount k → i ∈ A k ∨ i ∈ B k →
              IsLambdaCQuasiGeodesicWord D lambda c (word k i)) →
            (∀ k i, i < sideCount k → i ∉ B k →
              HullSC.RelWord.IsAdmissible D (word k i) ∧ (word k i).length ≤ eps) →
            (n : ℝ) * Real.sqrt (rho : ℝ) ≤
              ∑ k : Fin d, classWordLength (word k) (sideCount k) (A k) →
            ∃ k : Fin d, ∃ C : WordConnectorPair D (v k) (word k) (sideCount k) (A k) (B k) eps,
              Nonempty (NonemptyConnectors C)

theorem unboundComponentNonemptyConnectors : UnboundComponentNonemptyConnectorsStatement.{u, w} := by
  intro G _ Lambda D hsymm delta lambda c mu hdelta hdelta0 hlambda hc hmu
  obtain ⟨kappa, hkappa, eps, rho0, hrho0, hcomponents⟩ :=
    unboundComponentWordPolygons G Lambda D delta lambda c mu hdelta hdelta0 hlambda hc hmu
  refine ⟨kappa, hkappa, eps, rho0, hrho0, ?_⟩
  intro rho hrho
  obtain ⟨scale, hproduce⟩ := hcomponents rho hrho
  refine ⟨scale, ?_⟩
  intro n d hn arcCount sideCount v word A B hcount hsides hclose hends hquasi hshort htotal
  obtain ⟨k, ⟨C⟩⟩ := hproduce n d hn arcCount sideCount v word A B
    hcount hsides hclose hends hquasi hshort htotal
  exact ⟨k, C, C.nonempty_connectors_at_scale hsymm scale hdelta0 hkappa⟩

end GroupApproximation.GGT.VanKampen.UnboundEstimate

#audit_closed_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.unboundComponentNonemptyConnectors
