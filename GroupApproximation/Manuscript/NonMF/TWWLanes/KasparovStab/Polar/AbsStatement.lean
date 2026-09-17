import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Endpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# Kasparov stabilization: the absolute-value interface for the polar unitary

Lane `nm-tww-17` splits the remaining gap `PolarUnitaryStatement` (Lance, Prop. 3.8) of lane
`nm-tww-16` into two parts.

* `AbsOperatorStatement B`: every adjointable `T : E → F` out of a complete module has an
  "absolute value" `S : E → E`.  This means `⟨Sx, Sx⟩ = ⟨Tx, Tx⟩` for every `x`, and the range of
  `T⋆T` lies in the closure of the range of `S`.
* `polarUnitary_of_absOperator`: the isometric extension argument (Lance, Thm. 3.5), proved in
  `Polar/Extend*.lean`.

Truth check: take `S = |T| = (T⋆T)^{1/2}`, the square root in the C⋆-algebra `L(E)`.  This is a
C⋆-algebra because `E` is complete.  Then `⟨|T|x, |T|x⟩ = ⟨|T|²x, x⟩ = ⟨T⋆Tx, x⟩ = ⟨Tx, Tx⟩`.
Also `T⋆T x = |T| (|T| x)` lies in the range of `|T|`.  The statement is strictly smaller than
`PolarUnitaryStatement`: it names one operator, and says nothing about unitaries, density, or
the target module being complete.
-/

namespace GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab

open GroupApproximation.HilbertModule

universe v

/-- Absolute value of an adjointable operator out of a complete module (interface of lane
`nm-tww-17`, square-root part). -/
def AbsOperatorStatement (B : Type v) [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] : Prop :=
  ∀ (E F : CStarModule.{v, v} B) (T : Adjointable E F), IsCompleteModule E →
    ∃ S : Adjointable E E,
      (∀ x : E.carrier, E.inner (S.toFun x) (S.toFun x) = F.inner (T.toFun x) (T.toFun x)) ∧
      ∀ x : E.carrier, IsApprox S (T.adj (T.toFun x))

end GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOperatorStatement
