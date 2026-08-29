import GroupApproximation.Analysis.CStarSeparableTypeZeroRepresentation
import GroupApproximation.Analysis.ShulmanFillNormingTailRecognition

/-!
# Gelfand--Naimark with the dimension clause, discharged

`ShulmanFill.SeparableFaithfulInfiniteRepresentationStatement` is the input the
repaired binder needs: a faithful representation on a separable Hilbert space in
`Type 0` that is also infinite-dimensional.  It was named as owed in
`Analysis/ShulmanFillNormingTailRecognition`; this module proves it.

Nothing new is built.  `CStarState.exists_typeZero_faithful_representation`
carries the clause since
`Analysis/CStarInfiniteDimensionalGNS.not_finiteDimensional_familyGNSSpace`
showed the GNS sum has an orthonormal sequence and `b.repr` transported it, so
the statement is that theorem read off at `B`.

With this, the repaired route's second owed input is closed and only
`ShiftedPrintedMFStatement` remains — the same input the unshifted route has,
which `Analysis/ShulmanFillNormingEllTwoTheorem10` discharges there and which
`Analysis/ShulmanFillNormingTailPrintedPair`'s docstring records what is known
about discharging here.
-/

namespace GroupApproximation
namespace CStarState

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

/-- **The dimension-strengthened Gelfand--Naimark input is a theorem.** -/
theorem separableFaithfulInfiniteRepresentation :
    ShulmanFill.SeparableFaithfulInfiniteRepresentationStatement.{u} := by
  intro B _ _ _
  exact exists_typeZero_faithful_representation

end

end CStarState
end GroupApproximation
