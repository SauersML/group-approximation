import GroupApproximation.Analysis.CollapseDiscardCoordinates

/-!
# The `q`-normalized Hilbert space, set up from `q` alone

Proof-ledger row `CO.20`, the opening of the paragraph *The `q`-normalized
Hilbert space*:

> Take a self-adjoint bounded lift `(x_n)` of `q` … continuous functional
> calculus makes `Q_n = χ_{[1/2,∞)}(x_n)` a projection … the sequence `(Q_n)`
> again lifts `q`.  Since `q ≠ 0`, `Q_n ≠ 0` for infinitely many `n`; discard
> the remaining coordinates, relabel by `ℕ`, and put `k_n = rank Q_n ≥ 1`.

Both halves of that passage are proved — `CollapseProjectionLift` produces the
projection lift by continuous functional calculus, and
`CollapseDiscardCoordinates` shows the discarding is a choice of ultrafilter
rather than a reindexing.  This file states the passage as one step, which is
how the printed proof uses it: from a nonzero projection of the corona, a
projection lift *and* a free ultrafilter along which its rank is positive, in
a single `obtain`.

Everything the rank-normalized Hilbertization needs about `q` is then in hand,
and no clause of it is a hypothesis of the caller.
-/

namespace GroupApproximation
namespace CollapseNormalizedSetup

open Filter Matrix Topology
open KazhdanCornerMatrices

noncomputable section

variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]

/-- **The printed setup of the `q`-normalized Hilbert space.**

A nonzero projection of the corona has a projection lift together with a free
ultrafilter along which the lift's rank is positive.  The lift is the printed
`Q_n = χ_{[1/2,∞)}(x_n)`; the ultrafilter is the printed *"discard the
remaining coordinates"*, which is a choice rather than a reindexing.

This is the single step the rest of the collapse proof consumes: with it,
`Λ` is defined, `‖Λ(q)‖ = 1` holds, and the nonvanishing argument closes. -/
theorem exists_projection_lift_and_ultrafilter
    (q : NormMatrixCStarCorona (fun n ↦ Y n)) (hsa : star q = q)
    (hidem : q * q = q) (hne : q ≠ 0) :
    ∃ (Q : BoundedMatrixSequence (fun n ↦ Y n)) (ω : Ultrafilter ℕ),
      (∀ n, IsOrthogonalProjectionMatrix (Q n)) ∧
        normMatrixCStarCoronaMk (fun n ↦ Y n) Q = q ∧
        (ω : Filter ℕ) ≤ cofinite ∧
        ∀ᶠ n in (ω : Filter ℕ), 0 < (Q n).rank := by
  obtain ⟨Q, hQproj, hQmk⟩ :=
    CollapseProjectionLift.exists_projection_lift Y q hsa hidem
  have hQne : normMatrixCStarCoronaMk (fun n ↦ Y n) Q ≠ 0 := by
    rw [hQmk]
    exact hne
  obtain ⟨ω, hωcof, hωrk⟩ :=
    CollapseDiscardCoordinates.exists_free_ultrafilter_rank_pos Y Q hQproj hQne
  exact ⟨Q, ω, hQproj, hQmk, hωcof, hωrk⟩

end

end CollapseNormalizedSetup
end GroupApproximation
