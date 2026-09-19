import GroupApproximation.Analysis.VoiculescuStageSelection

/-!
# (V1b) The diagonal: one sequence that is quasicentral for all the targets

`Analysis/VoiculescuStageSelection` produces, for each finite prefix of the
target family and each tolerance, a single average of late members of the
sequential unit that commutes with that prefix to within the tolerance.  The
quasicentral unit is the diagonal of those stages: at stage `m` take the first
`m` targets and tolerance `1/(m+1)`, and require the average to be assembled
from members of index at least `m`.

Both limit clauses fall out of that choice, and they fall out differently.
The commutator clause is a squeeze: for `m > k` the `k`-th commutator is
below `1/(m+1)` by construction.  The absorption clause is *not* a squeeze
against the `m`-th member — an average of late members is not controlled by any
single one of them — but against the whole tail: the stage's last clause says
the average inherits any bound that all members from `m` on satisfy, and for a
compact `T` those bounds shrink because the unit absorbs `T`.  This is why the
stage carries that clause in the "for every `d`" form rather than as a numeric
bound.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

/-- **(V1b), from (V1a)'s output.**  A sequential approximate unit for the
compacts can be replaced by one that is asymptotically central for a given
countable family of bounded operators, keeping compactness, self-adjointness,
contractivity and the absorption. -/
theorem exists_quasicentral_of_sequentialCompactUnit (u : SequentialCompactUnit H)
    (S : ℕ → (H →L[ℂ] H)) :
    ∃ e : ℕ → (H →L[ℂ] H),
      (∀ n, IsCompactOperator (e n)) ∧
      (∀ n, IsSelfAdjoint (e n)) ∧
      (∀ n, ‖e n‖ ≤ 1) ∧
      (∀ k, Tendsto (fun n ↦ ‖e n * S k - S k * e n‖) atTop (𝓝 0)) ∧
      (∀ T : H →L[ℂ] H, IsCompactOperator T →
        Tendsto (fun n ↦ ‖T - e n * T‖) atTop (𝓝 0)) := by
  have hstage : ∀ m : ℕ, ∃ f : H →L[ℂ] H, IsCompactOperator f ∧ IsSelfAdjoint f ∧
      ‖f‖ ≤ 1 ∧ (∀ k < m, ‖f * S k - S k * f‖ ≤ 1 / ((m : ℝ) + 1)) ∧
      (∀ (T : H →L[ℂ] H) (d : ℝ),
        (∀ n, m ≤ n → ‖T - u.toFun n * T‖ ≤ d) → ‖T - f * T‖ ≤ d) := by
    intro m
    exact exists_stage_of_sequentialCompactUnit u S m m (by positivity)
  choose f hfc hfsa hfnorm hfcomm hfabs using hstage
  refine ⟨f, hfc, hfsa, hfnorm, ?_, ?_⟩
  · intro k
    refine squeeze_zero' (Eventually.of_forall fun m ↦ norm_nonneg _) ?_
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine eventually_atTop.2 ⟨k + 1, fun m hm ↦ ?_⟩
    exact hfcomm m k (by omega)
  · intro T hT
    refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
    obtain ⟨m₀, hm₀⟩ := Metric.tendsto_atTop.1 (u.tendsto_left T hT) (ε / 2) (by linarith)
    refine ⟨m₀, fun m hm ↦ ?_⟩
    have hbound : ‖T - f m * T‖ ≤ ε / 2 := by
      refine hfabs m T (ε / 2) fun n hn ↦ ?_
      have h := hm₀ n (le_trans hm hn)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h
      exact h.le
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    linarith

end

end ShulmanFill
end GroupApproximation
