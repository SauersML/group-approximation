import GroupApproximation.Analysis.OmegaHilbertComplete
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The printed word "Hilbert", as a closed proposition

The printed proof of the Kazhdan transport result says

> Regard `M_{d_n}(ℂ)` as a Hilbert space with its normalized Hilbert--Schmidt
> inner product, and form the Hilbert-space ultraproduct `K_ω`.

Two files supply the two halves of that word.  `Sofic/KOmegaHilbert.lean`
descends the ultralimit pairing to `K_ω` and registers mathlib's
`InnerProductSpace ℂ`, positive definiteness proved rather than assumed;
`Analysis/OmegaHilbertComplete.lean` registers `CompleteSpace`, by the
absolutely-convergent-series criterion applied to representatives truncated so
that their coordinate masses obey a bound at *every* stage.

Both halves are instances, and instances are invisible to the endpoint audit:
`#audit_closed_axioms` looks at one named constant, and there was no constant
that said the two hold together.  This file supplies one.  `KOmegaIsHilbertSpace`
is a closed proposition -- `Y`, `w`, `ω` and the weight hypothesis are
universally quantified inside it, not supplied by a caller -- and
`manuscriptKOmegaIsHilbertSpace` proves it.

## Why the orthogonality clauses are here

`CompleteSpace` alone would be a property nothing reads.  The printed proof uses
`K_ω` as a Hilbert space in exactly one way: it takes the orthogonal complement
of the fixed subspace and decomposes along it.  Both clauses below are the
statements that fail without completeness and hold with it:

* `Kᗮᗮ = K.topologicalClosure` is `Submodule.orthogonal_orthogonal_eq_closure`,
  whose mathlib docstring records a counterexample in an incomplete inner
  product space, so this clause is a genuine consumer of `kOmegaCompleteSpace`
  and not a restatement of it;
* `IsCompl K.topologicalClosure (K.topologicalClosure)ᗮ` is the orthogonal
  decomposition itself, available because a closed subspace of a complete space
  is complete and therefore admits an orthogonal projection.

Nothing is assumed: the proof term is `inferInstance` and two mathlib lemmas
applied to the instances the two construction files register.
-/

namespace GroupApproximation
namespace KOmegaHilbertSpaceEndpoint

open KOmegaHilbert OmegaHilbertComplete

/-- **KT.05, as a closed proposition: `K_ω` is a Hilbert space.**

For every sequence of finite models, every nonnegative weight and every
ultrafilter on `ℕ`, the manuscript's `K_ω` is complete, and consequently the
orthogonal complement operation on its subspaces behaves as it does in a
Hilbert space: the double complement of a subspace is its closure, and a closed
subspace is complemented by its orthogonal complement.

The inner product itself is not a clause: it is the `InnerProductSpace ℂ`
instance of `KOmegaHilbert.kOmegaInnerProductSpace`, without which `Kᗮ` below
would not even elaborate. -/
def KOmegaIsHilbertSpace : Prop :=
  ∀ (Y : ℕ → FiniteModel) (w : ℕ → ℝ) (ω : Ultrafilter ℕ) (hw : ∀ n, 0 ≤ w n),
    CompleteSpace (KOmega Y w ω hw) ∧
      ∀ K : Submodule ℂ (KOmega Y w ω hw),
        Kᗮᗮ = K.topologicalClosure ∧
          IsCompl K.topologicalClosure (K.topologicalClosure)ᗮ

/-- **The printed Hilbert-space ultraproduct, proved.**

`inferInstance` is `OmegaHilbertComplete.kOmegaCompleteSpace`, found by
typeclass search rather than named, which is the point: the instance is the one
any downstream consumer of `K_ω` picks up, so this endpoint certifies the same
object those consumers use. -/
theorem manuscriptKOmegaIsHilbertSpace : KOmegaIsHilbertSpace :=
  fun _Y _w _ω _hw ↦
    ⟨inferInstance, fun K ↦
      ⟨Submodule.orthogonal_orthogonal_eq_closure K,
        (K.topologicalClosure).isCompl_orthogonal⟩⟩

#audit_closed_axioms manuscriptKOmegaIsHilbertSpace

end KOmegaHilbertSpaceEndpoint
end GroupApproximation
