import GroupApproximation.GGT.VanKampen.Estimating.Unbound
import GroupApproximation.Meta.AxiomGuard

/-!
# The simultaneous scale choice in Osin's unbound-arc argument

In arXiv:math/0411039v3, Appendix §9, equation (36) chooses epsilon after
the hyperbolicity and quasi-geodesic constants.  Lemma 9.4 then takes rho
large enough for both the polygon-density estimate and strict shortening
of a cutting path.  The later uncovered-budget conversion imposes another
lower bound on rho.

This module proves those numerical choices simultaneously and uniformly in
all larger rho.  The geometric constants `c1`, `c2`, and `kappa` remain
explicit inputs: this is not a proof of the complementary-region surgery
or of the current `EstimatingUnboundOutputStatement` (see issue #198).
-/

namespace GroupApproximation.GGT.VanKampen.UnboundEstimate

/-- The scale inequalities actually used in the unbound-arc argument.
The density quantity is `a = lambda * sqrt rho / 240 - c`. -/
structure OsinUnboundScale (lambda c mu kappa c1 c2 : ℝ) (eps rho : ℕ) : Prop where
  epsilon_large : c1 + 2 * kappa < (eps : ℝ)
  rho_pos : 0 < rho
  density_large : max (1000 * (eps : ℝ)) c2 <
    lambda * Real.sqrt (rho : ℝ) / 240 - c
  shortcut_shortens : (eps : ℝ) <
    (lambda * Real.sqrt (rho : ℝ) / 240 - c) / 1000 - 2 * kappa
  threshold : 1 ≤ 2 * mu * Real.sqrt (rho : ℝ)

/-- Once epsilon exceeds the closeness bound, one positive rho threshold
works for every larger relator-length threshold. -/
theorem exists_osinUnboundScale_after_epsilon
    (lambda c mu kappa c1 c2 : ℝ) (hlambda : 0 < lambda) (hmu : 0 < mu)
    (eps : ℕ) (heps : c1 + 2 * kappa < (eps : ℝ)) :
    ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
      OsinUnboundScale lambda c mu kappa c1 c2 eps rho := by
  let bound : ℝ := max (max (1000 * (eps : ℝ)) c2)
    (1000 * ((eps : ℝ) + 2 * kappa))
  obtain ⟨rhoGeometry, hrhoGeometry, hgeometry⟩ :=
    exists_nat_sqrt_threshold lambda c bound hlambda
  obtain ⟨rhoBudget, _, hbudget⟩ := exists_two_mu_sqrt_threshold mu hmu
  refine ⟨max rhoGeometry rhoBudget,
    lt_of_lt_of_le hrhoGeometry (Nat.le_max_left _ _), ?_⟩
  intro rho hrho
  have hgeo : rhoGeometry ≤ rho := le_trans (Nat.le_max_left _ _) hrho
  have hbud : rhoBudget ≤ rho := le_trans (Nat.le_max_right _ _) hrho
  have ha := hgeometry rho hgeo
  refine {
    epsilon_large := heps
    rho_pos := lt_of_lt_of_le hrhoGeometry hgeo
    density_large := lt_of_le_of_lt (le_max_left _ _) ha
    shortcut_shortens := ?_
    threshold := hbudget rho hbud }
  have hshort : 1000 * ((eps : ℝ) + 2 * kappa) <
      lambda * Real.sqrt (rho : ℝ) / 240 - c :=
    lt_of_le_of_lt (le_max_right _ _) ha
  linarith

/-- The source's order of choices: first epsilon, then a uniform rho
threshold.  Neither choice needs a bound on the number of relator cells. -/
theorem exists_osinUnboundScale_parameters
    (lambda c mu kappa c1 c2 : ℝ) (hlambda : 0 < lambda) (hmu : 0 < mu) :
    ∃ eps rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
      OsinUnboundScale lambda c mu kappa c1 c2 eps rho := by
  obtain ⟨eps, heps⟩ := exists_nat_gt (c1 + 2 * kappa)
  obtain ⟨rho0, hrho0, hscale⟩ :=
    exists_osinUnboundScale_after_epsilon lambda c mu kappa c1 c2 hlambda hmu eps heps
  exact ⟨eps, rho0, hrho0, hscale⟩

/-- The uncovered-budget threshold alone does not imply the strict
shortening margin, even with valid positive lambda and mu.  This illustrates
the missing scale information; it does not refute the diagram statement. -/
theorem budget_threshold_without_shortening_margin :
    (1 : ℝ) ≤ 2 * (1 / 16) * Real.sqrt (64 : ℝ) ∧
      ¬ (0 : ℝ) < (1 * Real.sqrt (64 : ℝ) / 240 - 1) / 1000 - 2 * 0 := by
  have hsqrt : Real.sqrt (64 : ℝ) = 8 := by
    norm_num
  rw [hsqrt]
  norm_num

end GroupApproximation.GGT.VanKampen.UnboundEstimate

#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.exists_osinUnboundScale_parameters
#audit_closed_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.budget_threshold_without_shortening_margin
