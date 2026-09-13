import GroupApproximation.GGT.VanKampen.ClosedWalkPinchSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# Excising a lobe from a closed dart walk

A closed dart walk that starts two of its darts at one vertex, at positions `i < j`, contains the
closed walk of the darts between them, the *lobe*.  Removing the lobe leaves a closed dart walk,
and its value is the value of the walk when the lobe reads `1`.

* `IsClosedDartWalk.lobe`: the darts at positions `i, …, j - 1` form a closed dart walk.
* `IsClosedDartWalk.excise`: the darts before `i` and from `j` on form a closed dart walk.
* `listVal_dartWord_eq_mul_lobe` and `listVal_dartWord_excise_of_lobe_eq_one`: the values.

These are the steps for excising a lobe that reads `1` from a pocket walk (Lemma 9.4, Case 1).
`ClosedWalkFaceColouring.closedChain_split` is the chain-level split at the front of the walk.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.4, Case 1).  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open GroupApproximation.HullSC

universe u w v

namespace IsClosedDartWalk

variable {M : CombMap.{v}} {walk : List M.Dart}

/-- Consecutive darts of a closed dart walk chain. -/
theorem vertexOf_alpha_getElem (hw : IsClosedDartWalk M walk) {i : ℕ} (hi : i + 1 < walk.length) :
    M.vertexOf (M.alpha walk[i]) = M.vertexOf walk[i + 1] := by
  obtain ⟨_, hchain, _⟩ := hw
  exact List.isChain_iff_getElem.mp hchain i hi

/-- The last dart of a closed dart walk ends where the first begins. -/
theorem vertexOf_alpha_getElem_last (hw : IsClosedDartWalk M walk) (h0 : 0 < walk.length) :
    M.vertexOf (M.alpha walk[walk.length - 1]) = M.vertexOf walk[0] := by
  obtain ⟨hne, _, hclose⟩ := hw
  simpa only [List.getLast_eq_getElem, List.head_eq_getElem] using hclose

/-- **Rotating a closed dart walk keeps it closed**, through the chain-level
`ClosedWalkFaceColouring.closedChain_append_comm`. -/
theorem append_comm {P Q : List M.Dart} (hw : IsClosedDartWalk M (P ++ Q)) :
    IsClosedDartWalk M (Q ++ P) := by
  obtain ⟨hne, hcc⟩ := isClosedDartWalk_iff_closedChain.mp hw
  refine isClosedDartWalk_iff_closedChain.mpr
    ⟨fun h => hne ?_, ClosedWalkFaceColouring.closedChain_append_comm hcc⟩
  obtain ⟨hQ, hP⟩ := List.append_eq_nil_iff.mp h
  rw [hP, hQ, List.nil_append]

/-- The rotation of a closed dart walk that starts at position `i`. -/
theorem rotate_at (hw : IsClosedDartWalk M walk) (i : ℕ) :
    IsClosedDartWalk M (walk.drop i ++ walk.take i) := by
  have h : IsClosedDartWalk M (walk.take i ++ walk.drop i) := by
    rwa [List.take_append_drop]
  exact h.append_comm

/-- The dart at position `m` of the rotation starting at `i`, for `m` before the wrap. -/
theorem getElem_rotate_at {i m : ℕ} (him : i + m < walk.length) :
    (walk.drop i ++ walk.take i)[m]'(by
      rw [List.length_append, List.length_drop, List.length_take]; omega) =
      walk[i + m] := by
  rw [List.getElem_append_left (by rw [List.length_drop]; omega), List.getElem_drop]

/-- **The lobe.**  If two darts at positions `i < j` start at one vertex, the darts at positions
`i, …, j - 1` form a closed dart walk. -/
theorem lobe (hw : IsClosedDartWalk M walk) {i j : ℕ} (hij : i < j) (hj : j < walk.length)
    (hpinch : M.vertexOf walk[i] = M.vertexOf walk[j]) :
    IsClosedDartWalk M ((walk.drop i).take (j - i)) := by
  have hrot := hw.rotate_at i
  have hlen : j - i < (walk.drop i ++ walk.take i).length := by
    rw [List.length_append, List.length_drop, List.length_take]
    omega
  have h0 := getElem_rotate_at (walk := walk) (i := i) (m := 0) (by omega)
  have hk := getElem_rotate_at (walk := walk) (i := i) (m := j - i) (by omega)
  have hidx : i + (j - i) = j := by omega
  have hpinch' : M.vertexOf (walk.drop i ++ walk.take i)[0] =
      M.vertexOf (walk.drop i ++ walk.take i)[j - i] := by
    rw [h0, hk]
    simpa only [Nat.add_zero, hidx] using hpinch
  have hlobe := hrot.take (k := j - i) (by omega) hlen hpinch'
  rwa [List.take_append_of_le_length (by rw [List.length_drop]; omega)] at hlobe

/-- **The walk with the lobe removed.**  If two darts at positions `i < j` start at one vertex,
the darts before position `i` and from position `j` on form a closed dart walk. -/
theorem excise (hw : IsClosedDartWalk M walk) {i j : ℕ} (hij : i < j) (hj : j < walk.length)
    (hpinch : M.vertexOf walk[i] = M.vertexOf walk[j]) :
    IsClosedDartWalk M (walk.take i ++ walk.drop j) := by
  have hrot := hw.rotate_at i
  have hlen : j - i < (walk.drop i ++ walk.take i).length := by
    rw [List.length_append, List.length_drop, List.length_take]
    omega
  have h0 := getElem_rotate_at (walk := walk) (i := i) (m := 0) (by omega)
  have hk := getElem_rotate_at (walk := walk) (i := i) (m := j - i) (by omega)
  have hidx : i + (j - i) = j := by omega
  have hpinch' : M.vertexOf (walk.drop i ++ walk.take i)[0] =
      M.vertexOf (walk.drop i ++ walk.take i)[j - i] := by
    rw [h0, hk]
    simpa only [Nat.add_zero, hidx] using hpinch
  have hrest := hrot.drop (k := j - i) hlen hpinch'
  rw [List.drop_append_of_le_length (by rw [List.length_drop]; omega), List.drop_drop,
    Nat.add_sub_cancel' hij.le] at hrest
  exact hrest.append_comm

end IsClosedDartWalk

section Values

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}

/-- **The value of a walk, around a lobe.** -/
theorem listVal_dartWord_eq_mul_lobe (Delta : DiscDiagram.{u, w, v} W)
    (walk : List Delta.toCombMap.Dart) {i j : ℕ} (hij : i ≤ j) :
    GGT.RelLetter.listVal (Embedded.dartWord Delta walk) =
      GGT.RelLetter.listVal (Embedded.dartWord Delta (walk.take i)) *
        GGT.RelLetter.listVal (Embedded.dartWord Delta ((walk.drop i).take (j - i))) *
          GGT.RelLetter.listVal (Embedded.dartWord Delta (walk.drop j)) := by
  have hsplit : walk = walk.take i ++ (walk.drop i).take (j - i) ++ walk.drop j := by
    conv_lhs => rw [← List.take_append_drop i walk]
    rw [List.append_assoc]
    congr 1
    conv_lhs => rw [← List.take_append_drop (j - i) (walk.drop i)]
    rw [List.drop_drop, Nat.add_sub_cancel' hij]
  conv_lhs => rw [hsplit]
  rw [Embedded.dartWord_append, Embedded.dartWord_append, RelWord.listVal_append,
    RelWord.listVal_append]

/-- **Excising a lobe that reads `1` keeps the value.** -/
theorem listVal_dartWord_excise_of_lobe_eq_one (Delta : DiscDiagram.{u, w, v} W)
    (walk : List Delta.toCombMap.Dart) {i j : ℕ} (hij : i ≤ j)
    (hlobe : GGT.RelLetter.listVal (Embedded.dartWord Delta ((walk.drop i).take (j - i))) = 1) :
    GGT.RelLetter.listVal (Embedded.dartWord Delta (walk.take i ++ walk.drop j)) =
      GGT.RelLetter.listVal (Embedded.dartWord Delta walk) := by
  rw [listVal_dartWord_eq_mul_lobe Delta walk hij, hlobe, mul_one, Embedded.dartWord_append,
    RelWord.listVal_append]

end Values

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsClosedDartWalk.vertexOf_alpha_getElem
#audit_axioms GroupApproximation.GGT.VanKampen.IsClosedDartWalk.vertexOf_alpha_getElem_last
#audit_axioms GroupApproximation.GGT.VanKampen.IsClosedDartWalk.lobe
#audit_axioms GroupApproximation.GGT.VanKampen.IsClosedDartWalk.excise
#audit_axioms GroupApproximation.GGT.VanKampen.listVal_dartWord_eq_mul_lobe
#audit_axioms GroupApproximation.GGT.VanKampen.listVal_dartWord_excise_of_lobe_eq_one
