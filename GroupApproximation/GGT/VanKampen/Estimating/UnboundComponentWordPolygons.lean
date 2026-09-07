import GroupApproximation.GGT.VanKampen.Estimating.UnboundDenseComponent
import GroupApproximation.GGT.VanKampen.Estimating.UnboundWordConnectors

/-!
# The metric contradiction in a family of complementary polygons

One uniform choice of parameters handles every finite family of actual
cyclic word polygons. If their first-class word lengths reach the global
unbound threshold, the `53n` arc budget and fourfold cutting bound select a
strictly dense component. The proved word-polygon theorem constructs a
forward source segment, a target segment, and the two short geodesic words.

Constructing this polygon family from the complementary regions, and showing
that its connector pair contradicts the chosen diagram's minimality, remain
the topological steps of Osin's Appendix Lemma 9.4.
-/

namespace GroupApproximation.GGT.VanKampen.UnboundEstimate

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-- Uniform parameters and an actual connector pair in one complementary
word polygon. Every metric and finite-selection witness is produced. -/
def UnboundComponentWordPolygonsStatement : Prop :=
  ∀ (G : Type u) [Group G] (Lambda : Type w) (D : RelGenSet G Lambda)
    (δ lambda c mu : ℝ),
    IsHyperbolicSpace δ (Cayley D.alphabet) → 0 ≤ δ →
    0 < lambda → 0 ≤ c → 0 < mu →
    ∃ kappa : ℝ, 0 ≤ kappa ∧ ∃ eps rho0 : ℕ, 0 < rho0 ∧
      ∀ rho : ℕ, rho0 ≤ rho →
        OsinUnboundScale lambda c mu kappa (12 * ((δ + 6) + 1))
          (100000 * ((δ + 6) + 1)) eps rho ∧
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
            ∃ k : Fin d,
              Nonempty (WordConnectorPair D (v k) (word k) (sideCount k) (A k) (B k) eps)

theorem unboundComponentWordPolygons : UnboundComponentWordPolygonsStatement.{u, w} := by
  intro G _ Lambda D δ lambda c mu hδ hδ0 hlambda hc hmu
  obtain ⟨kappa, hkappa, eps, rho0, hrho0, hpolygon⟩ :=
    unboundWordPolygon G Lambda D δ lambda c mu hδ hδ0 hlambda hc hmu
  refine ⟨kappa, hkappa, eps, rho0, hrho0, ?_⟩
  intro rho hrho
  obtain ⟨scale, hpairs⟩ := hpolygon rho hrho
  refine ⟨scale, ?_⟩
  intro n d hn arcCount sideCount v word A B hcount hsides hclose hends hquasi hshort htotal
  have hsqrt : 0 < Real.sqrt (rho : ℝ) := Real.sqrt_pos.mpr
    (by exact_mod_cast lt_of_lt_of_le hrho0 hrho)
  obtain ⟨k, hdense⟩ := exists_component_gt_twoForty n hn (Real.sqrt (rho : ℝ)) hsqrt
    arcCount sideCount (fun k => classWordLength (word k) (sideCount k) (A k))
    hcount hsides htotal
  have pair := hpairs (sideCount k) (v k) (word k) (A k) (B k) (hclose k)
    (hends k) (hquasi k) (hshort k) hdense
  exact ⟨k, pair.exists_connectors (fun i hi hiAB => (hquasi k i hi hiAB).1)⟩

end GroupApproximation.GGT.VanKampen.UnboundEstimate

#audit_closed_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.unboundComponentWordPolygons
