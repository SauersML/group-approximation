import GroupApproximation.Analysis.VoiculescuStrongToNorm

/-!
# (V1a) A sequential unit from any strongly convergent contraction sequence

`Analysis/VoiculescuStrongToNorm` proved the analytic step: against a compact
operator, strong convergence to the identity is norm convergence.  This module
spends it, turning any sequence of compact self-adjoint contractions converging
strongly to `1` into a `SequentialCompactUnit`.

Splitting it out means the construction of such a sequence — orthogonal
projections onto the spans of a dense sequence's prefixes — can be probed on its
own, and that whatever produces the projections can change without touching the
reduction.  Nothing here needs `H` separable: separability enters only where the
projections are built.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

/-- **The reduction.**  A sequence of compact self-adjoint contractions
converging strongly to the identity is a sequential approximate unit for the
compacts.  The only analytic input is `strongToNormOnCompacts`. -/
def sequentialCompactUnitOfProjections (hSN : StrongToNormOnCompactsStatement)
    (P : ℕ → (H →L[ℂ] H)) (hcompact : ∀ n, IsCompactOperator (P n))
    (hsa : ∀ n, IsSelfAdjoint (P n)) (hnorm : ∀ n, ‖P n‖ ≤ 1)
    (hstrong : ∀ v : H, Tendsto (fun n ↦ P n v) atTop (𝓝 v)) :
    SequentialCompactUnit H where
  toFun := P
  isCompact := hcompact
  isSelfAdjoint := hsa
  norm_le := hnorm
  tendsto_left := hSN H P hnorm hstrong

/-- **What the construction still owes**: a sequence of finite-rank orthogonal
projections increasing to the identity on a separable space.

Named rather than inlined so it can be probed on its own.  The intended witness
is the orthogonal projection onto the span of the first `n` terms of a dense
sequence: `orthogonalProjectionOnto` composed with the subspace inclusion,
self-adjoint and contractive because orthogonal projections are, compact because
its range is finite-dimensional, and strongly convergent because the projection
realises the distance to a subspace whose union is dense.

Two of those are not in Mathlib at the pin under a name I could find: that a
finite-rank operator is compact, and the monotonicity in `n` that turns "the
distance to the spans tends to zero" into convergence rather than merely a
liminf. -/
def SeparableProjectionSequenceStatement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H],
    ∃ P : ℕ → (H →L[ℂ] H),
      (∀ n, IsCompactOperator (P n)) ∧
      (∀ n, IsSelfAdjoint (P n)) ∧
      (∀ n, ‖P n‖ ≤ 1) ∧
      (∀ v : H, Tendsto (fun n ↦ P n v) atTop (𝓝 v))

/-- **(V1a), modulo the projections.**  With the analytic step proved and the
projections supplied, every separable Hilbert space has a sequential compact
unit. -/
theorem exists_sequentialCompactUnit (hSN : StrongToNormOnCompactsStatement)
    (hP : SeparableProjectionSequenceStatement) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] :
    Nonempty (SequentialCompactUnit H) := by
  obtain ⟨P, hcompact, hsa, hnorm, hstrong⟩ := hP H
  exact ⟨sequentialCompactUnitOfProjections hSN P hcompact hsa hnorm hstrong⟩

end

end ShulmanFill
end GroupApproximation
