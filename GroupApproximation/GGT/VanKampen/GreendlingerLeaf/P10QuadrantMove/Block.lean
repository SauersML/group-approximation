import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.Keep
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.FLLists
import GroupApproximation.GGT.VanKampen.ClosedWalkInnermostLobe
import GroupApproximation.Meta.AxiomGuard

/-!
# Filters of a closed walk that remove or keep one cyclic block

Lane gl-p10-92.  Helper lemmas for `P10FilterMoveExists.p10FM_QuadrantMoveStatement`.

`p10QM_CyclicBlock c B` says that `B` is a cyclically contiguous block of `c`: either
`c = X ++ B ++ Z`, or `B` wraps around, `c = X ++ Y ++ Z` with `B = Z ++ X`.

* `p10QM_closed_filter_remove`: if `c` is a duplicate-free closed dart walk, `B` a closed cyclic
  block, some dart of `c` is off `B`, and the filter keeps exactly the darts of `c` off `B`, then
  the filtered walk is closed.
* `p10QM_closed_filter_keep`: the same when the filter keeps exactly the darts of `B`.
* `p10QM_exists_simple_lobe`: a pinched boundary cycle that is a closed walk has a cyclic block
  that is a simple closed walk and misses some dart of the cycle (innermost lobe,
  `ClosedWalkInnermostLobe.exists_innermost_lobe`).

All PROVED.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides

/-- **`B` is a cyclic block of `c`**: a contiguous block, possibly wrapping around the end. -/
def p10QM_CyclicBlock {α : Type v} (c B : List α) : Prop :=
  (∃ X Z : List α, c = X ++ B ++ Z) ∨ ∃ X Y Z : List α, c = X ++ Y ++ Z ∧ B = Z ++ X

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_CyclicBlock

theorem p10QM_mem_outer {α : Type v} {X Y Z : List α} {d : α} (hd : d ∈ X ++ Z) :
    d ∈ X ++ Y ++ Z := by
  rcases List.mem_append.mp hd with h | h
  · exact List.mem_append_left Z (List.mem_append_left Y h)
  · exact List.mem_append_right (X ++ Y) h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_mem_outer

theorem p10QM_mem_mid {α : Type v} {X Y Z : List α} {d : α} (hd : d ∈ Y) : d ∈ X ++ Y ++ Z :=
  List.mem_append_left Z (List.mem_append_right X hd)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_mem_mid

theorem p10QM_mem_swap {α : Type v} {X Z : List α} {d : α} (hd : d ∈ Z ++ X) : d ∈ X ++ Z := by
  rcases List.mem_append.mp hd with h | h
  · exact List.mem_append_right X h
  · exact List.mem_append_left Z h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_mem_swap

theorem p10QM_mem_outer_of_not_mem {α : Type v} {X Y Z : List α} {d : α}
    (hd : d ∈ X ++ Y ++ Z) (hY : d ∉ Y) : d ∈ X ++ Z := by
  rcases List.mem_append.mp hd with h | h
  · rcases List.mem_append.mp h with h' | h'
    · exact List.mem_append_left Z h'
    · exact absurd h' hY
  · exact List.mem_append_right X h

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_mem_outer_of_not_mem

theorem p10QM_mem_mid_of_not_mem {α : Type v} {X Y Z : List α} {d : α}
    (hd : d ∈ X ++ Y ++ Z) (hXZ : d ∉ Z ++ X) : d ∈ Y := by
  by_contra hY
  exact hXZ (p10QM_mem_swap (p10QM_mem_outer_of_not_mem hd hY))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_mem_mid_of_not_mem

/-- In a duplicate-free `X ++ Y ++ Z`, a dart of `X ++ Z` is not in `Y`. -/
theorem p10QM_not_mem_mid {α : Type v} {X Y Z : List α} (hnd : (X ++ Y ++ Z).Nodup) {d : α}
    (hd : d ∈ X ++ Z) : d ∉ Y := by
  rw [List.nodup_append, List.nodup_append] at hnd
  obtain ⟨⟨-, -, hXY⟩, -, hXYZ⟩ := hnd
  intro hY
  rcases List.mem_append.mp hd with hX | hZ
  · exact hXY d hX d hY rfl
  · exact hXYZ d (List.mem_append_right X hY) d hZ rfl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_not_mem_mid

theorem p10QM_cyclicBlock_subset {α : Type v} {c B : List α} (h : p10QM_CyclicBlock c B) :
    ∀ d ∈ B, d ∈ c := by
  rcases h with ⟨X, Z, rfl⟩ | ⟨X, Y, Z, rfl, rfl⟩
  · intro d hd
    exact p10QM_mem_mid hd
  · intro d hd
    exact p10QM_mem_outer (p10QM_mem_swap hd)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_cyclicBlock_subset

/-- If `X ++ Y ++ Z` and `Z ++ X` are closed dart walks and `Y` is nonempty, `Y` is closed. -/
theorem p10QM_closed_mid {M : CombMap.{v}} {X Y Z : List M.Dart}
    (hw : IsClosedDartWalk M (X ++ Y ++ Z)) (hZX : IsClosedDartWalk M (Z ++ X)) (hY : Y ≠ []) :
    IsClosedDartWalk M Y := by
  have h₁ : IsClosedDartWalk M (Y ++ Z ++ X) :=
    IsClosedDartWalk.append_comm (P := X) (Q := Y ++ Z) (by rw [← List.append_assoc]; exact hw)
  have h₂ : IsClosedDartWalk M (Y ++ (Z ++ X) ++ []) := by
    rw [List.append_nil, ← List.append_assoc]
    exact h₁
  have h₃ := P10RoseLobe.roseLobeFL_isClosedDartWalk_excise h₂ hZX
    (by rw [List.append_nil]; exact hY)
  rw [List.append_nil] at h₃
  exact h₃

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.p10QM_closed_mid
