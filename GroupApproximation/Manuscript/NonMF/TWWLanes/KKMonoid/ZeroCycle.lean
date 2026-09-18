import Mathlib.Algebra.Module.PUnit
import GroupApproximation.Analysis.KasparovBimodule
import GroupApproximation.Meta.AxiomGuard

/-!
# The zero Kasparov bimodule

`zeroModule B` is the zero Hilbert `B`-module.  Its carrier is `PUnit` and its inner product is
`0`.  `zeroCycle A B` is the Kasparov bimodule on it, with every operator `0`.  It is
degenerate, and it is the zero element of the KK monoid.

## The proof route

* Every clause about vectors is an equation in `PUnit`, so it holds by `rfl` (unit eta).
* Every clause about `B`-values is `0 = 0 + 0`, `0 = c • 0`, `0 = 0 * b`, `star 0 = 0`, or the
  positivity of `0` (`OrderZero.isPositiveElem_zero`).
* The boundedness and compactness clauses come from `Adjointable.isCompactOp_zero`, moved along a
  pointwise `rfl` (`Adjointable.IsCompactOp.congr`).
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace KKMonoidLane

open HilbertModule

universe u v w

section Plain

variable (B : Type v) [NonUnitalCStarAlgebra B]

/-- **The zero Hilbert module.** -/
@[reducible] def zeroModule : CStarModule.{v, w} B where
  carrier := PUnit.{w + 1}
  act _ _ := PUnit.unit
  inner _ _ := 0
  act_add_left _ _ _ := rfl
  act_add_right _ _ _ := rfl
  act_assoc _ _ _ := rfl
  act_smul _ _ _ := rfl
  inner_add_right _ _ _ := by
    show (0 : B) = 0 + 0
    exact (add_zero (0 : B)).symm
  inner_smul_right c _ _ := by
    show (0 : B) = c • (0 : B)
    exact (smul_zero c).symm
  inner_act_right _ _ b := by
    show (0 : B) = 0 * b
    exact (zero_mul b).symm
  inner_star _ _ := by
    show star (0 : B) = 0
    exact star_zero
  inner_self_isPositive _ := OrderZero.isPositiveElem_zero
  inner_self_eq_zero _ _ := rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.zeroModule

end Plain

variable (A : Type u) [NonUnitalCStarAlgebra A]
variable (B : Type v) [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **The zero Kasparov bimodule**: the zero module, with zero grading, representation and
operator. -/
def zeroCycle : KasparovBimodule.{u, v, w} A B where
  E := zeroModule.{v, w} B
  grading := Adjointable.zero _ _
  pi _ := Adjointable.zero _ _
  op := Adjointable.zero _ _
  grading_bounded := Adjointable.IsCompactOp.isBounded Adjointable.isCompactOp_zero
  grading_selfAdjoint _ := rfl
  grading_involutive _ := rfl
  rep :=
    { bounded := fun _ => Adjointable.IsCompactOp.isBounded Adjointable.isCompactOp_zero
      map_add := fun _ _ _ => rfl
      map_smul := fun _ _ _ => rfl
      map_mul := fun _ _ _ => rfl
      map_star := fun _ _ => rfl }
  rep_even _ _ := rfl
  op_bounded := Adjointable.IsCompactOp.isBounded Adjointable.isCompactOp_zero
  op_odd _ := rfl
  compact_one _ :=
    Adjointable.IsCompactOp.congr (T := Adjointable.zero _ _) (fun _ => rfl)
      Adjointable.isCompactOp_zero
  compact_selfAdjoint _ :=
    Adjointable.IsCompactOp.congr (T := Adjointable.zero _ _) (fun _ => rfl)
      Adjointable.isCompactOp_zero
  compact_commutator _ :=
    Adjointable.IsCompactOp.congr (T := Adjointable.zero _ _) (fun _ => rfl)
      Adjointable.isCompactOp_zero

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.zeroCycle

/-- **The zero bimodule is degenerate.** -/
theorem zeroCycle_isDegenerate : IsDegenerate (zeroCycle.{u, v, w} A B) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.zeroCycle_isDegenerate

end KKMonoidLane
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
