import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Polar.AbsStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Polar unitary, lane `nm-tww-17b`: boundedness of adjointable maps (statement)

The extension argument of Lance, Thm. 3.5 / Prop. 3.8 uses one analytic input: the adjoint
`T⋆` of an adjointable map between complete modules is bounded. The corpus does not supply
this, because a bundled `CStarModule` need not be complete
(`Analysis/CStarAdjointableNorm.lean`, module docstring).

`AdjointableBoundedStatement B`: every adjointable map between complete modules is bounded.
This is the closed graph theorem for Hilbert modules. It is true: the graph of an adjointable
map is closed, since `⟨z, y⟩ = lim ⟨z, T uₙ⟩ = lim ⟨T⋆z, uₙ⟩ = ⟨T⋆z, x⟩ = ⟨z, T x⟩`.
It is proved in `Polar/ExtendClosedGraph.lean` from Mathlib's closed graph theorem.
The statement is kept in its own module so that the reduction
`polarUnitary_of_absOperator_of_adjointableBounded` does not depend on the normed-space
plumbing.
-/

namespace GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab

open GroupApproximation.HilbertModule

universe v

/-- **Closed graph theorem for Hilbert modules**: an adjointable map between complete modules
is bounded. -/
def AdjointableBoundedStatement (B : Type v) [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] : Prop :=
  ∀ (E F : CStarModule.{v, v} B) (T : Adjointable E F), IsCompleteModule E →
    IsCompleteModule F → T.IsBounded

end GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AdjointableBoundedStatement
