import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Polar.ExtendAdjoint
import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Polar.ExtendClosedGraph
import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Polar.ExtendDense
import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Polar.ExtendPolarize
import GroupApproximation.Meta.AxiomGuard

/-!
# Polar unitary, lane `nm-tww-17b`: endpoint

`polarUnitary_of_absOperator : AbsOperatorStatement B → PolarUnitaryStatement B`
(Lance, Thm. 3.5 / Prop. 3.8), and the composite
`kasparovStabilization_of_absOperator : AbsOperatorStatement B → KasparovStabilizationStatement B`.

Assembly. Let `T : E → F` be adjointable between complete modules, with `T` and `T⋆` of dense
range. Take `S` from `AbsOperatorStatement`.
1. `T⋆` is bounded (`isBounded_of_isCompleteModule`, the closed graph theorem).
2. `S` has dense range (`hasDenseRange_of_approx_adjoint_comp`).
3. `⟨Tx, Ty⟩ = ⟨Sx, Sy⟩` (`inner_eq_inner_of_diag`).
4. `Sx ↦ Tx` extends to `W : E → F` (`F` complete, `S` dense). `Tx ↦ Sx` extends to
   `V : F → E` (`E` complete, `T` dense) (`exists_isometricExtension`).
5. `⟨W u, v⟩ = ⟨u, V v⟩`, `V ∘ W = id` and `W ∘ V = id` (`Polar/ExtendAdjoint.lean`). So
   `U = (W, V)` is an adjointable unitary.

The only remaining input is `AbsOperatorStatement` (the square root `|T| = (T⋆T)^{1/2}`), which
belongs to the square-root half of lane `nm-tww-17`.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab

open GroupApproximation.HilbertModule

universe v

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **Lance, Prop. 3.8, from the absolute value**: an adjointable map between complete modules
with dense range and dense adjoint range has a unitary phase. -/
theorem polarUnitary_of_absOperator (h : AbsOperatorStatement B) : PolarUnitaryStatement B := by
  intro E F T hE hF hT hT'
  obtain ⟨S, hdiag, happrox⟩ := h E F T hE
  have hb : (Adjointable.adjoint T).IsBounded :=
    isBounded_of_isCompleteModule (Adjointable.adjoint T) hF hE
  have hS : HasDenseRange S := hasDenseRange_of_approx_adjoint_comp T S happrox hT hT' hb
  obtain ⟨W, hW⟩ := exists_isometricExtension S T (fun x => (hdiag x).symm) hS hF
  obtain ⟨V, hV⟩ := exists_isometricExtension T S hdiag hT hE
  have hinner : ∀ x y : E.carrier,
      F.inner (T.toFun x) (T.toFun y) = E.inner (S.toFun x) (S.toFun y) :=
    fun x y => (inner_eq_inner_of_diag S T hdiag x y).symm
  let U : Adjointable E F :=
    { toFun := W
      adj := V
      inner_adj := isometricExtension_inner S T hW hV hinner hS hT }
  have hU : U.IsUnitaryAdj :=
    { adj_toFun := isometricExtension_leftInverse S T hW hV hS
      toFun_adj := isometricExtension_leftInverse T S hV hW hT }
  exact ⟨U, hU⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.polarUnitary_of_absOperator

/-- **Kasparov stabilization from the absolute value.** -/
theorem kasparovStabilization_of_absOperator (h : AbsOperatorStatement B) :
    KasparovStabilizationStatement B :=
  kasparovStabilization_of_polarUnitary (polarUnitary_of_absOperator h)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.kasparovStabilization_of_absOperator

end GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab
