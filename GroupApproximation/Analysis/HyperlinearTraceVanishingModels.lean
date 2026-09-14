import GroupApproximation.Sofic.HyperlinearUltraproduct
import GroupApproximation.Sofic.HyperlinearAmplification
import GroupApproximation.Meta.AxiomGuard

/-!
# Trace-preserving unitary matrix models of hyperlinear groups

Statement module of lane `oa-mcduff` (absorbed from oa-ozawa71) for `simple_kazhdan_sofic_group.tex`
at origin/main 37551fd93, "Brown's formulation", tex 276–278 (census row `fc6e6384121b`): "So `L(G)`
embeds in `𝓡^ω` [Kirchberg, Radulescu], [Ozawa, Proposition 7.1]".  The first step of that proposition
turns separated unitary models into models whose normalized traces converge to the canonical trace
`δ_{g,1}`.  Lane oa-llp consumes the same models for "`C*(G)` does not have the local lifting property".

* `TracePreservingMatrixModel G`: exact unitaries `map n g ∈ U(model n)`, asymptotically multiplicative
  in normalized Hilbert–Schmidt distance (`AsymptoticUnitaryRepresentation`), with
  `normTrace (map n 1) → 1` and `normTrace (map n g) → 0` for `g ≠ 1`.
* `HasTracePreservingMatrixModel G`: such a model exists.
* `HyperlinearTracePreservingModelStatement`: every countable hyperlinear group has one.  The proof,
  by amplifying separated models `V = (1 ⊕ u)^{⊗a} ⊗ (1 ⊕ ū)^{⊗a}`, is the next module's work.
-/

namespace GroupApproximation

open Filter Matrix

universe u

/-- **A trace-preserving unitary matrix model** of `G`: exact unitaries in finite models, asymptotically
multiplicative in normalized Hilbert–Schmidt distance, whose normalized traces converge to the
canonical trace `δ_{g,1}`. -/
structure TracePreservingMatrixModel (G : Type u) [Group G] extends
    AsymptoticUnitaryRepresentation G where
  /-- The normalized traces of the models of `1` tend to `1`. -/
  trace_tendsto_one :
    Tendsto (fun n ↦ normTrace (model n) (map n 1 : Matrix (model n) (model n) ℂ)) atTop (nhds 1)
  /-- The normalized traces of the models of `g ≠ 1` tend to `0`. -/
  trace_tendsto_ne : ∀ g : G, g ≠ 1 →
    Tendsto (fun n ↦ normTrace (model n) (map n g : Matrix (model n) (model n) ℂ)) atTop (nhds 0)

/-- `G` has a trace-preserving unitary matrix model. -/
def HasTracePreservingMatrixModel (G : Type u) [Group G] : Prop :=
  Nonempty (TracePreservingMatrixModel G)

/-- **Countable hyperlinear groups have trace-preserving unitary matrix models**: the matrix half of
Ozawa's Proposition 7.1.  Stated here; the amplification proof is the next module's work. -/
def HyperlinearTracePreservingModelStatement : Prop :=
  ∀ (G : Type u) [Group G] [Countable G], IsHyperlinear G → HasTracePreservingMatrixModel G

end GroupApproximation
