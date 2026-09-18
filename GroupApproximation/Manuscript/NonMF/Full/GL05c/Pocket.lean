import GroupApproximation.Manuscript.NonMF.Full.GL05c.Diagram
import Mathlib.Tactic.IntervalCases
import GroupApproximation.Meta.AxiomGuard

/-!
# The pocket of the counterexample to WO-GL05-2'

The pocket `pocketK : PocketFaceSet D 1 diagram 0 4` on the diagram of `Full/GL05c/Diagram.lean`,
with the hypotheses of `GL05c.ExtremalEndBlockStatement`.

* Faces `{P, R1, Q1, R2, Q2}` (`pocketFaces`).  The boundary cycle is `[8,12,10,0,2,6,4]`.
* `t_1 = [11,13,9]` on the source cell `S`, so `t_1⁻¹ = [8,12,10]`.  Then `s_1 = []`, `s_2 = [0]`
  (the loop `p`), and `t_2 = [2,6,4]` on the exterior.
* `closedWalk`: consecutive darts meet at a vertex.
* `not_firstTurns`: the turn from `10` to `0` at `w` is not a first turn.
* `not_unpinched`: the darts `8` and `0` both start at `w`.
* `allNonFirstTurnsCrossed`: the turns at `8`, `12`, `2`, `6` are first turns.  The three passages
  at `w` (after `10`, `0` and `4`) cross each other.

## Manuscript status

Infrastructure for `thm:hull` (`non_mf_groups_exist.tex`, tex 2121, Hull's small cancellation
theorem, through Osin's Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL05c.Model

open Equiv GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.OsinPocketPinchedTwoGonModel (G gx gy D)

/-! ## The face set and its boundary cycle -/

/-- The faces `P, R1, Q1, R2, Q2` (indices below `5`). -/
noncomputable def pocketFaces : Finset diagram.toCombMap.Face :=
  Finset.univ.filter fun f => faceEquiv f < 5

theorem mem_pocketFaces (d : Fin 16) : M.faceOf d ∈ pocketFaces ↔ faceClass d < 5 := by
  unfold pocketFaces
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ _)

theorem isBoundaryDart_iff (d : Fin 16) :
    Surgery.MapCollapse.IsBoundaryDart diagram.toCombMap pocketFaces d ↔
      d ∈ ([8, 12, 10, 0, 2, 6, 4] : List diagram.toCombMap.Dart) := by
  change M.faceOf d ∈ pocketFaces ∧ M.faceOf (M.alpha d) ∉ pocketFaces ↔ _
  rw [mem_pocketFaces d, mem_pocketFaces (M.alpha d)]
  fin_cases d <;> decide

/-- The boundary cycle `t_1⁻¹ s_2 t_2 = [8,12,10] [0] [2,6,4]`. -/
noncomputable def pocketBoundary :
    Surgery.MapCollapse.BoundaryCycle diagram.toCombMap pocketFaces where
  cycle := [8, 12, 10, 0, 2, 6, 4]
  cycle_nonempty := List.cons_ne_nil _ _
  cycle_nodup := by decide
  cycle_mem_iff := fun d => (isBoundaryDart_iff d).symm

/-! ## The carrier arcs -/

/-- The arc `t_1 = [11,13,9]` of the source cell. -/
noncomputable def srcArc : Embedded.CyclicArc (Embedded.cellDarts diagram sIndex) where
  start := ⟨2, by rw [cellDarts_sIndex]; decide⟩
  length := 3
  length_le := by rw [cellDarts_sIndex]; decide

theorem srcArc_darts : srcArc.darts = [11, 13, 9] :=
  (congrArg (fun l : List diagram.toCombMap.Dart => (l.drop 2 ++ l.take 2).take 3)
    cellDarts_sIndex).trans rfl

/-- The arc `t_2 = [2,6,4]` of the exterior boundary. -/
noncomputable def tgtArc : Embedded.CyclicArc (Embedded.outerDarts diagram) where
  start := ⟨1, by rw [outerDarts_eq]; decide⟩
  length := 3
  length_le := by rw [outerDarts_eq]; decide

theorem tgtArc_darts : tgtArc.darts = [2, 6, 4] :=
  (congrArg (fun l : List diagram.toCombMap.Dart => (l.drop 1 ++ l.take 1).take 3)
    outerDarts_eq).trans rfl

/-! ## The pocket -/

/-- **The pocket of the counterexample**, with `eps = 1`, `lo = 0` and `hi = 4`. -/
noncomputable def pocketK : PocketFaceSet D 1 diagram 0 4 where
  faces := pocketFaces
  outerFace_not_mem := by
    change M.faceOf (faceRep 6) ∉ pocketFaces
    rw [mem_pocketFaces]
    decide
  source := sIndex
  source_not_mem := by
    change M.faceOf (faceRep 5) ∉ pocketFaces
    rw [mem_pocketFaces]
    decide
  kept := pIndex
  kept_mem := by
    change M.faceOf (faceRep 0) ∈ pocketFaces
    rw [mem_pocketFaces]
    decide
  sourceArc := srcArc
  targetArc := tgtArc
  firstSide := []
  secondSide := [0]
  boundary := pocketBoundary
  decomposition := by
    rw [srcArc_darts, tgtArc_darts]
    decide
  firstSide_length_le := by decide
  secondSide_length_le := by decide
  firstSide_norm_le := empty_side_norm
  secondSide_norm_le := one_side_norm
  lo_le := Nat.zero_le _
  le_hi := by decide

theorem pocketK_cycle : pocketK.boundary.cycle = [8, 12, 10, 0, 2, 6, 4] := rfl

/-! ## Helper facts -/

theorem vertexOf_eq {x y : diagram.toCombMap.Dart}
    (h : vertexEquiv (M.vertexOf x) = vertexEquiv (M.vertexOf y)) :
    diagram.toCombMap.vertexOf x = diagram.toCombMap.vertexOf y :=
  vertexEquiv.injective h

/-- `List.next` does not depend on the decidable-equality instance. -/
theorem next_eq_of_inst {α : Type*} (i₁ i₂ : DecidableEq α) (l : List α) (x : α) (h : x ∈ l) :
    @List.next α i₁ l x h = @List.next α i₂ l x h := by
  have : i₁ = i₂ := funext fun _ => funext fun _ => Subsingleton.elim _ _
  subst this
  rfl

theorem next_8 (i : DecidableEq diagram.toCombMap.Dart)
    (h : (8 : diagram.toCombMap.Dart) ∈ pocketK.boundary.cycle) :
    @List.next _ i pocketK.boundary.cycle 8 h = 12 :=
  (next_eq_of_inst i diagram_decidableEq _ _ h).trans
    (by decide : @List.next _ diagram_decidableEq pocketK.boundary.cycle 8 (by decide) = 12)

theorem next_12 (i : DecidableEq diagram.toCombMap.Dart)
    (h : (12 : diagram.toCombMap.Dart) ∈ pocketK.boundary.cycle) :
    @List.next _ i pocketK.boundary.cycle 12 h = 10 :=
  (next_eq_of_inst i diagram_decidableEq _ _ h).trans
    (by decide : @List.next _ diagram_decidableEq pocketK.boundary.cycle 12 (by decide) = 10)

theorem next_10 (i : DecidableEq diagram.toCombMap.Dart)
    (h : (10 : diagram.toCombMap.Dart) ∈ pocketK.boundary.cycle) :
    @List.next _ i pocketK.boundary.cycle 10 h = 0 :=
  (next_eq_of_inst i diagram_decidableEq _ _ h).trans
    (by decide : @List.next _ diagram_decidableEq pocketK.boundary.cycle 10 (by decide) = 0)

theorem next_0 (i : DecidableEq diagram.toCombMap.Dart)
    (h : (0 : diagram.toCombMap.Dart) ∈ pocketK.boundary.cycle) :
    @List.next _ i pocketK.boundary.cycle 0 h = 2 :=
  (next_eq_of_inst i diagram_decidableEq _ _ h).trans
    (by decide : @List.next _ diagram_decidableEq pocketK.boundary.cycle 0 (by decide) = 2)

theorem next_2 (i : DecidableEq diagram.toCombMap.Dart)
    (h : (2 : diagram.toCombMap.Dart) ∈ pocketK.boundary.cycle) :
    @List.next _ i pocketK.boundary.cycle 2 h = 6 :=
  (next_eq_of_inst i diagram_decidableEq _ _ h).trans
    (by decide : @List.next _ diagram_decidableEq pocketK.boundary.cycle 2 (by decide) = 6)

theorem next_6 (i : DecidableEq diagram.toCombMap.Dart)
    (h : (6 : diagram.toCombMap.Dart) ∈ pocketK.boundary.cycle) :
    @List.next _ i pocketK.boundary.cycle 6 h = 4 :=
  (next_eq_of_inst i diagram_decidableEq _ _ h).trans
    (by decide : @List.next _ diagram_decidableEq pocketK.boundary.cycle 6 (by decide) = 4)

theorem next_4 (i : DecidableEq diagram.toCombMap.Dart)
    (h : (4 : diagram.toCombMap.Dart) ∈ pocketK.boundary.cycle) :
    @List.next _ i pocketK.boundary.cycle 4 h = 8 :=
  (next_eq_of_inst i diagram_decidableEq _ _ h).trans
    (by decide : @List.next _ diagram_decidableEq pocketK.boundary.cycle 4 (by decide) = 8)

theorem mem_cycle_cases : ∀ d : diagram.toCombMap.Dart, d ∈ pocketK.boundary.cycle →
    d = 8 ∨ d = 12 ∨ d = 10 ∨ d = 0 ∨ d = 2 ∨ d = 6 ∨ d = 4 := by
  decide

/-- One rotation step from the reversed dart is a first turn. -/
theorem firstTurn_one {N : CombMap} {c : List N.Dart} {x y : N.Dart}
    (h : (N.sigma ^ 1) (N.alpha x) = y) : GL05c.FirstTurn N c x y :=
  ⟨1, Nat.one_pos, h, fun _ ht0 ht1 => absurd ht1 (Nat.not_lt.mpr ht0)⟩

theorem not_iff_of_pos_neg {p q : Prop} (hp : p) (hq : ¬q) : ¬(p ↔ q) := fun h => hq (h.mp hp)

/-- A dart met after `y` is not inside the sector from `x` to `y`. -/
theorem not_rotationBetween_of_first {N : CombMap} {x y z : N.Dart} {a₀ : ℕ} (ha₀ : 0 < a₀)
    (h : (N.sigma ^ a₀) x = y) (hz : ∀ b, 0 < b → b < a₀ → (N.sigma ^ b) x ≠ z) :
    ¬ RotationBetween N x y z := by
  rintro ⟨a, ha, hza, hb⟩
  rcases Nat.lt_or_ge a a₀ with hlt | hge
  · exact hz a ha hlt hza
  · exact hb a₀ ha₀ hge h

/-! ## The three crossing passages at `w` -/

/-- Rotating from `α 10 = 11` meets `α 0 = 1` before `0`. -/
theorem rb_10_pos :
    RotationBetween diagram.toCombMap (diagram.toCombMap.alpha 10) 0 (diagram.toCombMap.alpha 0) :=
  ⟨3, by decide, by decide, fun b hb0 hba => by interval_cases b <;> decide⟩

/-- Rotating from `α 10 = 11` meets `0` before `2`. -/
theorem rb_10_neg :
    ¬ RotationBetween diagram.toCombMap (diagram.toCombMap.alpha 10) 0 2 :=
  not_rotationBetween_of_first (a₀ := 4) (by decide) (by decide)
    (fun b hb0 hb => by interval_cases b <;> decide)

/-- Rotating from `α 0 = 1` meets `α 4 = 5` before `2`. -/
theorem rb_0_pos :
    RotationBetween diagram.toCombMap (diagram.toCombMap.alpha 0) 2 (diagram.toCombMap.alpha 4) :=
  ⟨2, by decide, by decide, fun b hb0 hba => by interval_cases b <;> decide⟩

/-- Rotating from `α 0 = 1` meets `2` before `8`. -/
theorem rb_0_neg :
    ¬ RotationBetween diagram.toCombMap (diagram.toCombMap.alpha 0) 2 8 :=
  not_rotationBetween_of_first (a₀ := 3) (by decide) (by decide)
    (fun b hb0 hb => by interval_cases b <;> decide)

/-- Rotating from `α 4 = 5` meets `α 10 = 11` before `8`. -/
theorem rb_4_pos :
    RotationBetween diagram.toCombMap (diagram.toCombMap.alpha 4) 8 (diagram.toCombMap.alpha 10) :=
  ⟨3, by decide, by decide, fun b hb0 hba => by interval_cases b <;> decide⟩

/-- Rotating from `α 4 = 5` meets `8` before `0`. -/
theorem rb_4_neg :
    ¬ RotationBetween diagram.toCombMap (diagram.toCombMap.alpha 4) 8 0 :=
  not_rotationBetween_of_first (a₀ := 4) (by decide) (by decide)
    (fun b hb0 hb => by interval_cases b <;> decide)

/-! ## The hypotheses of `GL05c.ExtremalEndBlockStatement` -/

/-- **The boundary cycle is a closed walk.** -/
theorem closedWalk : pocketK.ClosedWalk := by
  refine ⟨?_, vertexOf_eq (by decide)⟩
  show List.IsChain _ ([8, 12, 10, 0, 2, 6, 4] : List diagram.toCombMap.Dart)
  exact .cons_cons (vertexOf_eq (by decide)) (.cons_cons (vertexOf_eq (by decide))
    (.cons_cons (vertexOf_eq (by decide)) (.cons_cons (vertexOf_eq (by decide))
      (.cons_cons (vertexOf_eq (by decide)) (.cons_cons (vertexOf_eq (by decide))
        (.singleton _))))))

/-- **`t_1` is a proper arc of `S`.** -/
theorem srcArc_length :
    pocketK.sourceArc.length < (Embedded.cellDarts diagram pocketK.source).length := by
  change 3 < (Embedded.cellDarts diagram sIndex).length
  rw [cellDarts_sIndex]
  decide

/-- **`t_2` is a proper arc of the exterior boundary.** -/
theorem tgtArc_length : pocketK.targetArc.length < (Embedded.outerDarts diagram).length := by
  change 3 < (Embedded.outerDarts diagram).length
  rw [outerDarts_eq]
  decide

/-- **The pocket is not in first-turn order**: from `α 0 = 1`, the first dart of the walk met at
`w` is `5 = α 4`, not `α 10 = 11`. -/
theorem not_firstTurns : ¬ GL05c.FirstTurns pocketK := by
  rintro ⟨hchain, -⟩
  change List.IsChain _ ([8, 12, 10, 0, 2, 6, 4] : List diagram.toCombMap.Dart) at hchain
  obtain ⟨k, hk0, hk, havoid⟩ := (List.isChain_cons_cons.mp
    (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hchain).2).2).1
  rcases Nat.lt_or_ge 1 k with h1 | h1
  · exact havoid 1 Nat.one_pos h1 (Or.inl (by decide))
  · obtain rfl : k = 1 := Nat.le_antisymm h1 hk0
    exact absurd hk (by decide)

/-- **The face set is pinched**: the boundary darts `8` and `0` both start at `w`. -/
theorem not_unpinched : ¬ GL05c.Unpinched diagram.toCombMap pocketK.faces := by
  intro h
  have h80 := h 8 0 ((isBoundaryDart_iff _).mpr (by decide))
    ((isBoundaryDart_iff _).mpr (by decide)) (vertexOf_eq (by decide))
  exact absurd h80 (by decide)

/-- **Every non-first turn is crossed.**  The turns at `8`, `12`, `2` and `6` are one rotation
step.  The passages at `w` after `10`, `0` and `4` cross pairwise. -/
theorem allNonFirstTurnsCrossed : GL05c.AllNonFirstTurnsCrossed pocketK := by
  intro d₀ hd₀ hnf
  rcases mem_cycle_cases d₀ hd₀ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hnf (firstTurn_one (by rw [next_8]; decide))).elim
  · exact (hnf (firstTurn_one (by rw [next_12]; decide))).elim
  · refine ⟨0, by decide, by decide,
      (CombMap.vertexOf_eq_iff _ _ _).mp (vertexOf_eq (by decide)), ?_⟩
    rw [next_10, next_0]
    exact not_iff_of_pos_neg rb_10_pos rb_10_neg
  · refine ⟨4, by decide, by decide,
      (CombMap.vertexOf_eq_iff _ _ _).mp (vertexOf_eq (by decide)), ?_⟩
    rw [next_0, next_4]
    exact not_iff_of_pos_neg rb_0_pos rb_0_neg
  · exact (hnf (firstTurn_one (by rw [next_2]; decide))).elim
  · exact (hnf (firstTurn_one (by rw [next_6]; decide))).elim
  · refine ⟨10, by decide, by decide,
      (CombMap.vertexOf_eq_iff _ _ _).mp (vertexOf_eq (by decide)), ?_⟩
    rw [next_4, next_10]
    exact not_iff_of_pos_neg rb_4_pos rb_4_neg

end GroupApproximation.Full.GL05c.Model

#audit_axioms GroupApproximation.Full.GL05c.Model.pocketK
#audit_axioms GroupApproximation.Full.GL05c.Model.closedWalk
#audit_axioms GroupApproximation.Full.GL05c.Model.not_firstTurns
#audit_axioms GroupApproximation.Full.GL05c.Model.not_unpinched
#audit_axioms GroupApproximation.Full.GL05c.Model.allNonFirstTurnsCrossed
