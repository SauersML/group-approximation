import GroupApproximation.Analysis.LIXLimitMatrixTransport
import GroupApproximation.Analysis.LIXEndpointStatement
import GroupApproximation.Analysis.LIXSimplicityInstance

/-!
# Packaging the inductive limit's data for its two consumers

`Analysis/LIXLimitMatrixTransport` assembles a `K₁`-non-injectivity witness for the inductive
limit of a tower of C⋆-algebras, and `Analysis/LIXLimitCompletion` exposes its stages as closed,
increasing, densely-union subalgebras.  Both are stated in the tower's own vocabulary; this file
repackages them into the exact shapes their two consumers ask for, so that the eventual
instantiation at the concrete LIX tower is a one-line application of each.

* `cs-endpoint`'s `HasK1InjWitness`, from `Analysis/LIXEndpointStatement` — `hasK1InjWitness_limit`
  below is `CStarTower.exists_unitary_witness` read at that name.  No new instance bookkeeping is
  needed: `HasK1InjWitness A` is a plain `def` unfolding to the same existential, so the term
  built under this file's own spectral-order instances is accepted by `isDefEq` unfolding both
  sides down to `CStarAlgebra.spectralOrder`/`spectralOrderedRing` — exactly the "`exact`, not
  `rw`" situation recorded in this lane's report.
* `cs-simplicity`'s `LIX.StagewiseFullTower`, from `Analysis/LIXSimplicityInstance` — the four
  structural facts the tower already proves (`stage`, `isClosed_stage`, `stage_mono`,
  `dense_iUnion_stage`) assemble into it as soon as stagewise fullness, the one piece of data
  genuinely specific to the LIX tower, is supplied as a hypothesis.
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

/-! ### The stages, packaged as a `StagewiseFullTower` -/

/-- **The stages of the inductive limit, packaged as a `StagewiseFullTower`.**  Given stagewise
fullness — the one input this tower does not derive on its own, supplied by the tower-specific
fullness argument — the four structural facts already proved about the stages assemble into
`LIX.StagewiseFullTower T.Limit`, ready for `StagewiseFullTower.isSimpleCStar`.  A `def`, not a
`theorem`: `StagewiseFullTower` bundles data, so its type is not a `Prop`.  The order instances
are local to this file only, so they cannot compete with any global instance on `T.Limit`; the
conclusion `IsSimpleCStar` mentions no order, so which valid spectral order is used here is
immaterial downstream. -/
noncomputable def stagewiseFullTower (T : CStarTower A)
    (full_stage : ∀ (k : ℕ) (a : T.Limit), a ∈ T.stage k → 0 ≤ a → a ≠ 0 →
      ∃ j, k ≤ j ∧ IsFullIn (T.stage j) a) :
    StagewiseFullTower T.Limit where
  stage := T.stage
  isClosed_stage := T.isClosed_stage
  mono_stage := T.stage_mono
  dense_stage := T.dense_iUnion_stage
  full_stage := full_stage

end CStarTower

end LIX

end GroupApproximation
