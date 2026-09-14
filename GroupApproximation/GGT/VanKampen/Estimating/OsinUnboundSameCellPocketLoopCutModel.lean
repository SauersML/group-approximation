import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellPocketModel
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSucc
import GroupApproximation.Meta.AxiomGuard

/-!
# A model test for the loop cut of a same-cell pocket

`SameCellPocketLoopCutStatement` (`Estimating/OsinUnboundSameCellPocketAssembly`) takes a same-face
bridge dart `d` of a relator cell `i`, oriented toward the exterior, with a relator cell other than
`i` on the far side, and gives a loop cut of `Δ`.  The route of this lane first reads the pocket as
an enclosed face set: the far faces, enclosed in successor form by the pocket walk `f d … fᵐ d`,
which is an arc of cell `i`.

The map is `SameCellPocketModel.pocketDiagram`, the island map of `ClosedWalkIslandModel` with the
exterior on the loop `[0]` and relator cells on the island `[4]` and the ring `[1,2,5,3]` around the
bridge `t = 2/3`.  At `d = 2`:

* `island_far`: the island cell has a dart on the far side of `t`, so every hypothesis of the loop
  cut statement holds here, with `SameCellPocketModel.two_mem`, `faceOf_alpha_two` and `oriented_two`.
* `enclosedFaceSetSucc`: the pocket walk `[5]` encloses `{island}` in successor form.  The closing
  turn from `α 5 = 4` passes `σ 4 = 3`, which is off the walk, and meets `5` after two rotations.
* `ringArc_darts`: the pocket walk is the arc of the ring at position `2` of length `1`.
* `island_mem`, `ring_not_mem`: the island cell is inside and the ring is outside.

So the enclosed face set that the route builds exists, and is not vacuous, on a concrete pocket
holding a relator cell.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 2121, through Osin's Lemmas 9.4 and 9.7); certifies
no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.SameCellPocketLoopCutModel

open Equiv SimpleClosedWalkSides Embedded ClosedWalkIslandModel SameCellPocketModel

/-- The far faces of `t`: the island. -/
def pocketFaces : Finset M.Face := {face 1}

/-- The pocket walk of `2`: the ring dart strictly between `2` and `3`. -/
def pocketWalk : List M.Dart := [5]

/-- **The island cell has a dart on the far side of `t`.** -/
theorem island_far :
    Relation.EqvGen (AvoidEdgeStep pocketDiagram.toCombMap 2) 4 (pocketDiagram.toCombMap.alpha 2) :=
  .rel _ _ (Or.inl (by decide))

theorem walkKeep_three : ¬ walkKeep M pocketWalk 3 := by
  unfold walkKeep
  decide

theorem walkKeep_five : walkKeep M pocketWalk 5 := by
  unfold walkKeep
  decide

/-- The first dart on an edge of the walk after `α 5` is `5`, after two rotations. -/
theorem first_turn {m : ℕ} (hm : 0 < m)
    (hkeep : walkKeep M pocketWalk ((M.sigma ^ m) (M.alpha 5)))
    (hmin : ∀ k, 0 < k → k < m → ¬ walkKeep M pocketWalk ((M.sigma ^ k) (M.alpha 5))) :
    (M.sigma ^ m) (M.alpha 5) = 5 := by
  rcases Nat.lt_or_ge m 2 with h | h
  · obtain rfl : m = 1 := by omega
    have h3 : (M.sigma ^ 1) (M.alpha 5) = 3 := by decide
    rw [h3] at hkeep
    exact absurd hkeep walkKeep_three
  · rcases Nat.lt_or_ge m 3 with h' | h'
    · obtain rfl : m = 2 := by omega
      decide
    · have h5 : (M.sigma ^ 2) (M.alpha 5) = 5 := by decide
      exact absurd (by rw [h5]; exact walkKeep_five) (hmin 2 (by omega) (by omega))

/-- **The pocket walk encloses the island, turning to its successor.** -/
theorem enclosedFaceSetSucc : EnclosedFaceSetSucc pocketDiagram pocketFaces pocketWalk where
  outerFace_not_mem := by
    change face 0 ∉ ({face 1} : Finset M.Face)
    rw [Finset.mem_singleton]
    exact (face_eq_iff 0 1).not.mpr (by decide)
  ne_nil := List.cons_ne_nil _ _
  nodup := by decide
  chain := List.isChain_singleton _
  closes := (vertexOf_eq_iff (M.alpha 5) 5).mpr (by decide)
  mem_iff := by
    intro d
    change d ∈ pocketWalk ↔ M.faceOf d ∉ ({face 1} : Finset M.Face) ∧
      (M.faceOf (M.alpha d) ∈ ({face 1} : Finset M.Face) ∨ M.alpha d ∈ pocketWalk)
    simp only [Finset.mem_singleton, faceOf_eq_face]
    fin_cases d <;> decide
  turn_mem := by
    intro x hx m hm hkeep hmin
    have hx5 : x = 5 := List.mem_singleton.mp hx
    subst hx5
    have h := first_turn hm hkeep hmin
    show (M.sigma ^ m) (M.alpha 5) ∈ pocketWalk
    rw [h]
    exact List.mem_singleton_self _
  turn_next := by
    intro i hi m hm hkeep hmin
    obtain rfl : i = 0 := by
      have : i < 1 := hi
      omega
    exact first_turn hm hkeep hmin

/-- The arc of the ring at position `2` of length `1`. -/
def ringArc : CyclicArc (cellDarts pocketDiagram ringIndex) where
  start := ⟨2, by rw [cellDarts_ringIndex]; decide⟩
  length := 1
  length_le := by rw [cellDarts_ringIndex]; decide

/-- **The pocket walk is an arc of the ring.** -/
theorem ringArc_darts : ringArc.darts = pocketWalk := by
  show ((cellDarts pocketDiagram ringIndex).drop 2 ++
      (cellDarts pocketDiagram ringIndex).take 2).take 1 = pocketWalk
  rw [cellDarts_ringIndex]
  rfl

theorem island_mem : cellIsland.face ∈ pocketFaces := Finset.mem_singleton_self _

theorem ring_not_mem : (cell pocketDiagram ringIndex).face ∉ pocketFaces := by
  change face 2 ∉ ({face 1} : Finset M.Face)
  rw [Finset.mem_singleton]
  exact (face_eq_iff 2 1).not.mpr (by decide)

end GroupApproximation.GGT.VanKampen.SameCellPocketLoopCutModel

#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketLoopCutModel.island_far
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketLoopCutModel.first_turn
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketLoopCutModel.enclosedFaceSetSucc
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketLoopCutModel.ringArc_darts
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketLoopCutModel.island_mem
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketLoopCutModel.ring_not_mem
