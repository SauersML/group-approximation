import GroupApproximation.Analysis.LIXLimitMatrixTransport
import GroupApproximation.Analysis.LIXEndpointStatement

/-!
# Packaging the inductive limit's witness for its endpoint consumer

`Analysis/LIXLimitMatrixTransport` assembles a `K₁`-non-injectivity witness for the inductive
limit of a tower of C⋆-algebras.  It is stated in the tower's own vocabulary; this file repackages
it into the exact shape `cs-endpoint`'s `HasK1InjWitness` (`Analysis/LIXEndpointStatement`) asks
for, so that the eventual instantiation at the concrete LIX tower is a one-line application.

`hasK1InjWitness_limit` below is `CStarTower.exists_unitary_witness` read at that name.  No new
instance bookkeeping is needed: `HasK1InjWitness A` is a plain `def` unfolding to the same
existential, so the term built under this file's own spectral-order instances is accepted by
`isDefEq` unfolding both sides down to `CStarAlgebra.spectralOrder`/`spectralOrderedRing` —
exactly the "`exact`, not `rw`" situation recorded in this lane's report.

The matching bridge for `cs-simplicity`'s `LIX.StagewiseFullTower` — packaging `stage`,
`isClosed_stage`, `stage_mono`, `dense_iUnion_stage` given stagewise fullness — is **not** here:
`cs-simplicity` is authoring its own `CStarTower.stagewiseFullTower` directly in
`Analysis/LIXSimplicityInstance.lean` (checked on disk during this session), taking the fullness
hypothesis in finite-stage language and transporting it via `nonneg_iff_of_injective` and
`isFullIn_of_isFull_map` — a strictly better interface than a limit-language hypothesis would be,
since it is exactly the form a stage lane can supply without ever reasoning about the limit.  An
earlier version of this file duplicated that name; removed in favour of theirs to avoid a
duplicate declaration once both land in the same build.
-/

namespace GroupApproximation

namespace LIX

namespace CStarTower

universe u

variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)]

attribute [local instance] GroupApproximation.LIX.instSpectralPartialOrder
                            GroupApproximation.LIX.instSpectralStarOrderedRing

/-! ### The witness, packaged as `HasK1InjWitness` -/

/-- **The LIX witness of the inductive limit, packaged exactly as `HasK1InjWitness`.**  Same
hypotheses as `exists_unitary_witness`; the conclusion is the named predicate the endpoint lane
consumes instead of the bare existential. -/
theorem hasK1InjWitness_limit (T : CStarTower A) {k : ℕ} (u : unitary (A k))
    (hstage : ∀ (j : ℕ) (hj : k ≤ j),
      unitaryHom (T.climbHom hj) u ∉ unitaryComponentOne (A j))
    (hdiag : diagOne u ∈ unitaryComponentOne (CStarMat 2 (A k))) :
    HasK1InjWitness T.Limit :=
  T.exists_unitary_witness u hstage hdiag

end CStarTower

end LIX

end GroupApproximation
