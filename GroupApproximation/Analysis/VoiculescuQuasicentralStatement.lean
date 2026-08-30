import GroupApproximation.Analysis.VoiculescuPlan

/-!
# The quasicentral approximate unit, with the hypothesis its prose carries

`Analysis/VoiculescuPlan.QuasicentralApproximateUnitStatement` quantifies over
every Hilbert space `H`, with no separability hypothesis, and in that form it is
false.  This module states the repaired version, which is the one the lane will
prove and the one the plan's own prose for **(V)** describes: "let `A` be a
separable unital C\*-algebra, `H` a separable Hilbert space".

## Why the unrepaired form fails

Not in the quasicentrality --- in the approximate-unit clause, and for a reason
that has nothing to do with commutators.  A sequential approximate unit for
`K(H)` exists exactly when `K(H)` is σ-unital, which happens exactly when `H` is
separable.

Concretely, take `H` non-separable and any `e : ℕ → B(H)` with every `e n`
compact.  Each `e n` has separable range, so the closed span `V` of the
countably many ranges is separable and `V ≠ H`; choose a unit `v ⊥ V` and let
`T` be the rank-one projection onto `ℂ v`, which is compact.  Then

    `‖T - e n T‖ ≥ ‖(T - e n T) v‖ = ‖v - e n v‖` ,

and `e n v ∈ V ⊥ v`, so `‖v - e n v‖² = 1 + ‖e n v‖² ≥ 1` for every `n`.  The
last clause fails for every candidate `e`, so the existential is unsatisfiable.

The first four clauses do not see this: `e = 0` satisfies compactness,
self-adjointness, the norm bound and the commutator clause.  The whole of the
refutation sits in the approximate-unit half.

## The record, and what it costs

Doctrine here is that a refuted form stays in the tree as a theorem `¬ old`,
the way `Analysis/ShulmanFillNormingPrintedPairRefuted` carries its own.  That
record is *owed* rather than written, because none of its three analytic inputs
is in Mathlib at the pinned revision: that a compact operator has separable
range; that `lp (fun _ : ℝ ↦ ℂ) 2` is not separable; and, for the sharper route
that avoids both, that a compact operator carries a weakly null sequence to a
norm null one, which is what makes `{r | ‖e δᵣ‖ ≥ ε}` finite and so lets one
choose `r` with `e n δᵣ = 0` for all `n` at once.

The risk the record guards against is lower here than it was for the printed
binder: `QuasicentralApproximateUnitStatement` is cited by nothing --- its own
module says so --- so nothing depends on it and no consumer can adopt it by
accident.  Until the analysis is funded, this docstring is the record.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

/-- **Arveson's quasicentral approximate units**, with the separability its
proof and its use both require.  For a separable `H` and a countable family `S`
generating a C\*-subalgebra of `B(H)`, the compacts have an approximate unit
that is asymptotically central for `S`.

This is `VoiculescuPlan.QuasicentralApproximateUnitStatement` with
`[TopologicalSpace.SeparableSpace H]` added, which is the only difference. -/
def QuasicentralApproximateUnitSeparableStatement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (S : ℕ → (H →L[ℂ] H)),
      ∃ e : ℕ → (H →L[ℂ] H),
        (∀ n, IsCompactOperator (e n)) ∧
        (∀ n, IsSelfAdjoint (e n)) ∧
        (∀ n, ‖e n‖ ≤ 1) ∧
        (∀ k, Tendsto (fun n ↦ ‖e n * S k - S k * e n‖) atTop (𝓝 0)) ∧
        (∀ T : H →L[ℂ] H, IsCompactOperator T →
          Tendsto (fun n ↦ ‖T - e n * T‖) atTop (𝓝 0))

/-- **The repaired statement implies the unrepaired one at every separable
space**, which is the whole of the difference between them: the repair removes
the spaces where the conclusion is unavailable and changes nothing where it is.

Stated as the model test of the repair.  A reader comparing the two Props should
see that the second asks for less only by asking it of less. -/
theorem quasicentralApproximateUnit_of_separable
    (h : QuasicentralApproximateUnitSeparableStatement)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (S : ℕ → (H →L[ℂ] H)) :
    ∃ e : ℕ → (H →L[ℂ] H),
      (∀ n, IsCompactOperator (e n)) ∧
      (∀ n, IsSelfAdjoint (e n)) ∧
      (∀ n, ‖e n‖ ≤ 1) ∧
      (∀ k, Tendsto (fun n ↦ ‖e n * S k - S k * e n‖) atTop (𝓝 0)) ∧
      (∀ T : H →L[ℂ] H, IsCompactOperator T →
        Tendsto (fun n ↦ ‖T - e n * T‖) atTop (𝓝 0)) :=
  h H S

end

end ShulmanFill
end GroupApproximation
