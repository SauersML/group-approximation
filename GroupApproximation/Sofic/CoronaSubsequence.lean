import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Subsequential vanishing does not vanish in a norm corona

Proposition 6.1 of the multi-mover dossier.  In the norm matrix corona
`∏ₙ M_{dₙ} / ⊕ₙ M_{dₙ}` the class of a bounded sequence vanishes exactly when
the operator norms tend to zero, so vanishing along one infinite subsequence is
not enough.  The obstruction is already visible for scalars, which is what this
file records: a nonnegative sequence can vanish identically along the even
indices while failing to converge to zero.

This is the elementary point that makes the historical finite-mover argument
insufficient on its own, and it is what the block-amplification repair of
Section 7 works around.
-/

namespace GroupApproximation
namespace CoronaSubsequence

/-- The alternating scalar sequence: zero at even indices, one at odd ones. -/
noncomputable def alt (n : ℕ) : ℝ := if Even n then 0 else 1

@[simp] theorem alt_even {n : ℕ} (h : Even n) : alt n = 0 := if_pos h

@[simp] theorem alt_odd {n : ℕ} (h : ¬ Even n) : alt n = 1 := if_neg h

theorem alt_nonneg (n : ℕ) : 0 ≤ alt n := by
  unfold alt; split <;> norm_num

theorem alt_two_mul (j : ℕ) : alt (2 * j) = 0 :=
  alt_even ⟨j, by ring⟩

theorem alt_two_mul_add_one (j : ℕ) : alt (2 * j + 1) = 1 := by
  refine alt_odd ?_
  simp [parity_simps]

/-- **Proposition 6.1.**  A nonnegative sequence may vanish at every even index
and still fail to tend to zero.  Since a corona class vanishes exactly when the
norms tend to zero, subsequential collapse does not kill a corona element. -/
theorem exists_vanishing_on_subsequence_not_tendsto_zero :
    ∃ x : ℕ → ℝ, (∀ n, 0 ≤ x n) ∧ (∀ j, x (2 * j) = 0) ∧
      ¬ Filter.Tendsto x Filter.atTop (nhds 0) := by
  refine ⟨alt, alt_nonneg, alt_two_mul, ?_⟩
  intro h
  have hball : ∀ᶠ n in Filter.atTop, alt n ∈ Metric.ball (0 : ℝ) (1 / 2) :=
    h (Metric.ball_mem_nhds 0 (by norm_num))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hball
  have hmem := hN (2 * N + 1) (by omega)
  rw [Metric.mem_ball, Real.dist_eq, alt_two_mul_add_one] at hmem
  norm_num at hmem

end CoronaSubsequence
end GroupApproximation
