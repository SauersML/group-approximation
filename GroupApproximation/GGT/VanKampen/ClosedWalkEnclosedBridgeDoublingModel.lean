import GroupApproximation.GGT.VanKampen.ClosedWalkIslandModel
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSucc
import GroupApproximation.Meta.AxiomGuard

/-!
# A model test for doubling the bridges of an enclosed face set

`EnclosedBridgeDoublingSuccStatement` (`ClosedWalkEnclosedSubdiagramPieces`) thickens every bridge edge
of an outside walk that turns to its successor, one edge at a time.  A bridge dart `d` of the walk,
whose reverse is also on the walk, is doubled inside its own face.  The inner-face surgery
`FaceEdgeDoubling.diagram` needs that face to be off the exterior; the exterior branch is
`OuterSpurThickening.diagram`.  This module shows that the exterior branch cannot be dropped.

The map is ms-traces-2's `ClosedWalkIslandModel`: six darts, relator loops `Π = [0]` and `I = [4]`,
a bridge `t = 2/3`, and the exterior face `[1,2,5,3]`, which runs along both sides of `t`.

* `enclosedFaceSetSucc`: the exterior walk `[1,2,5,3]` encloses `{Π, I}` and turns to its successor,
  since every turn is one face step.
* `bridgeDarts_length`: the walk has exactly two bridge darts, `2` and `3`.
* `faceOf_eq_outerFace`: every dart of the walk lies on the exterior face.  So no bridge dart of this
  walk admits the inner-face surgery, and the first doubling step is the exterior one.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 2121, through Osin's Lemmas 9.4 and 9.7); certifies
no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.BridgeDoublingModel

open Equiv SimpleClosedWalkSides ClosedWalkIslandModel

/-- **The island walk turns to its successor.** -/
theorem enclosedFaceSetSucc : EnclosedFaceSetSucc diagram islandFaces outerWalk where
  toEnclosedFaceSet := enclosedFaceSet
  turn_next := by
    intro i hi m hm _hkeep hfirst
    rcases Nat.lt_or_ge 1 m with h1 | h1
    · exact absurd (walkKeep_all _) (hfirst 1 Nat.one_pos h1)
    · obtain rfl : m = 1 := by omega
      rw [pow_one]
      have hall : ∀ (k : ℕ) (hk : k < 4),
          M.sigma (M.alpha (outerWalk[k]'hk)) = outerWalk[(k + 1) % 4]'(Nat.mod_lt _ (by decide)) := by
        decide
      exact hall i hi

/-- The walk has exactly two bridge darts: `2` and `3`, the two darts of `t`. -/
theorem bridgeDarts_length :
    (outerWalk.filter fun d => decide (M.alpha d ∈ outerWalk)).length = 2 := by
  decide

theorem bridge_mem : (2 : M.Dart) ∈ outerWalk ∧ M.alpha 2 ∈ outerWalk := by
  decide

/-- **Every dart of the walk lies on the exterior face**, so the inner-face doubling reaches no
bridge dart of this walk. -/
theorem faceOf_eq_outerFace : ∀ d ∈ outerWalk, diagram.toCombMap.faceOf d = diagram.outerFace := by
  intro d hd
  refine (faceOf_eq_face d 2).mpr ?_
  revert hd
  fin_cases d <;> decide

end GroupApproximation.GGT.VanKampen.BridgeDoublingModel

#audit_axioms GroupApproximation.GGT.VanKampen.BridgeDoublingModel.enclosedFaceSetSucc
#audit_axioms GroupApproximation.GGT.VanKampen.BridgeDoublingModel.bridgeDarts_length
#audit_axioms GroupApproximation.GGT.VanKampen.BridgeDoublingModel.bridge_mem
#audit_axioms GroupApproximation.GGT.VanKampen.BridgeDoublingModel.faceOf_eq_outerFace
