import GroupApproximation.Manuscript.NonMF.Full.GL05c.Diagram
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
  rw [mem_pocketFaces, mem_pocketFaces]
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

theorem srcArc_darts : srcArc.darts = [11, 13, 9] := by
  change ((Embedded.cellDarts diagram sIndex).drop 2 ++
    (Embedded.cellDarts diagram sIndex).take 2).take 3 = _
  rw [cellDarts_sIndex]
  rfl

/-- The arc `t_2 = [2,6,4]` of the exterior boundary. -/
noncomputable def tgtArc : Embedded.CyclicArc (Embedded.outerDarts diagram) where
  start := ⟨1, by rw [outerDarts_eq]; decide⟩
  length := 3
  length_le := by rw [outerDarts_eq]; decide

theorem tgtArc_darts : tgtArc.darts = [2, 6, 4] := by
  change ((Embedded.outerDarts diagram).drop 1 ++ (Embedded.outerDarts diagram).take 1).take 3 = _
  rw [outerDarts_eq]
  rfl

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
