import GroupApproximation.GGT.VanKampen.Estimating.UnboundOrientedWordPolygon
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94Pieces
import GroupApproximation.GGT.CayleyFourPointBridge
import GroupApproximation.Meta.AxiomGuard

/-!
# The metric half of Osin's Lemma 9.4, oriented

Osin, *Small cancellations over relatively hyperbolic groups and embedding
theorems*, arXiv:math/0411039v3, Appendix, proof of Lemma 9.4.  `OsinLemma94Pieces`
derives `OsinLemma94SectionStatement` from two pieces: `OsinLemma94AntiparallelMetricStatement`,
the metric half, and `OsinLemma94PlanarRunInput`, the diagram half.  This file proves
the metric half.

* `exists_component_dense_of_sideBudget`: if the components have at most `K n` sides,
  `K s < t` and their lengths sum to at least `n t`, then some component has
  `k_i s` less than its length.
* `osinLemma94AntiparallelMetric`: `OsinLemma94AntiparallelMetricStatement`.
  - The four-point hyperbolic Cayley graph is a hyperbolic space
    (`isHyperbolicSpace_cayley_of_fourPoint`).
  - `unboundOrientedWordPolygonMonotone` at `μ = 1` gives `ε0` and, for each `ε ≥ ε0`,
    a threshold `ρ1`.
  - For `ρ ≥ (K + 1)² ρ1` the theorem is applied at `ρ' = ρ / (K + 1)²`.  Then
    `K √ρ' / 240 < √ρ`, so the side budget selects a component with
    `k_i √ρ' / 240 < S_i`.
  - That component carries an `OrientedWordSidePair` and so an
    `OrientedWordConnectorPair`, whose target indices run backwards.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w

open GroupApproximation.GGT.VanKampen.UnboundEstimate

/-- **Selecting a dense component under a side budget.**  If `d` components have at
most `K n` sides in total, `0 < n`, `0 ≤ s`, `K s < t`, and their lengths sum to at least
`n t`, then some component has `k_i s` less than its length. -/
theorem exists_component_dense_of_sideBudget {d : ℕ} (n K : ℕ) (hn : 0 < n) {s t : ℝ}
    (hs : 0 ≤ s) (hst : (K : ℝ) * s < t) (sideCount : Fin d → ℕ) (len : Fin d → ℝ)
    (hbudget : ∑ k : Fin d, sideCount k ≤ K * n)
    (htotal : (n : ℝ) * t ≤ ∑ k : Fin d, len k) :
    ∃ k : Fin d, (sideCount k : ℝ) * s < len k := by
  by_contra hnone
  push Not at hnone
  have hsum : ∑ k : Fin d, len k ≤ (∑ k : Fin d, (sideCount k : ℝ)) * s := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun k _ => hnone k
  have hbudgetReal : ∑ k : Fin d, (sideCount k : ℝ) ≤ (K : ℝ) * n := by
    exact_mod_cast hbudget
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (∑ k : Fin d, (sideCount k : ℝ)) * s ≤ (K : ℝ) * n * s :=
    mul_le_mul_of_nonneg_right hbudgetReal hs
  have h2 := mul_lt_mul_of_pos_left hst hnReal
  linarith

/-- **The metric half of Lemma 9.4, oriented.**  For a four-point hyperbolic `Γ(G, A)`,
`0 < λ`, `0 ≤ c` and every side constant `K`, there are monotone thresholds such that
dense closed quasi-geodesic word polygons with at most `K n` sides carry a connector pair
whose target indices run backwards. -/
theorem osinLemma94AntiparallelMetric : OsinLemma94AntiparallelMetricStatement.{u, w} := by
  intro G _ Lambda D hhyper lambda c hlambda hc K
  obtain ⟨delta, hdelta⟩ := hhyper
  obtain ⟨_, _, eps0, hpolygon⟩ :=
    unboundOrientedWordPolygonMonotone G Lambda D (delta : ℝ) lambda c 1
      (isHyperbolicSpace_cayley_of_fourPoint D.alphabet hdelta) (by positivity)
      hlambda hc one_pos
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho1, hrho1, hpolygonEps⟩ := hpolygon eps heps
  refine ⟨(K + 1) ^ 2 * rho1, mul_pos (by positivity) hrho1, fun rho hrho => ?_⟩
  intro n d hn sideCount v word A B hbudget hclose hends hquasi hshort htotal
  obtain ⟨rho', hrho1', hdiv⟩ : ∃ rho' : ℕ, rho1 ≤ rho' ∧ rho' * (K + 1) ^ 2 ≤ rho :=
    ⟨rho / (K + 1) ^ 2, (Nat.le_div_iff_mul_le (by positivity)).mpr
      (by rw [Nat.mul_comm]; exact hrho), Nat.div_mul_le_self rho ((K + 1) ^ 2)⟩
  have hdivReal : (rho' : ℝ) * ((K : ℝ) + 1) ^ 2 ≤ (rho : ℝ) := by
    exact_mod_cast hdiv
  have hK : (0 : ℝ) ≤ (K : ℝ) + 1 := by positivity
  have hsqrt : Real.sqrt (rho' : ℝ) * ((K : ℝ) + 1) ≤ Real.sqrt (rho : ℝ) := by
    have h := Real.sqrt_le_sqrt hdivReal
    rwa [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hK] at h
  have hpos : 0 < Real.sqrt (rho' : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast lt_of_lt_of_le hrho1 hrho1')
  have hKs : 0 ≤ (K : ℝ) * Real.sqrt (rho' : ℝ) := by positivity
  have hst : (K : ℝ) * (Real.sqrt (rho' : ℝ) / 240) < Real.sqrt (rho : ℝ) := by
    linarith
  obtain ⟨k, hk⟩ := exists_component_dense_of_sideBudget n K hn
    (by positivity : (0 : ℝ) ≤ Real.sqrt (rho' : ℝ) / 240) hst sideCount
    (fun k => classWordLength (word k) (sideCount k) (A k)) hbudget htotal
  obtain ⟨_, hpairs⟩ := hpolygonEps rho' hrho1'
  have pair := hpairs (sideCount k) (v k) (word k) (A k) (B k) (hclose k) (hends k)
    (hquasi k) (hshort k) (by simpa only [mul_div_assoc] using hk)
  obtain ⟨C⟩ := pair.exists_connectors (fun i hi hiAB => (hquasi k i hi hiAB).1)
  exact ⟨k, C.toWordConnectorPair, C.target_backward⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.exists_component_dense_of_sideBudget
#audit_closed_axioms GroupApproximation.GGT.VanKampen.osinLemma94AntiparallelMetric
