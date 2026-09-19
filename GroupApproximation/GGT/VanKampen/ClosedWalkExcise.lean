import GroupApproximation.GGT.VanKampen.ClosedWalkPinchSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# Excising a pinched stretch from a closed dart walk

If a closed dart walk `A ++ B ++ C` returns, after the stretch `B`, to the vertex where `B` began
(the first darts of `B` and of `C` start at the same vertex), then `A ++ C` is again a closed dart
walk.  In index form: if `walk[i]` and `walk[j]` start at the same vertex, with `i < j` and `j`
a position of the walk, then `walk.take i ++ walk.drop j` is a closed dart walk.

The proof rotates the walk to `C ++ A ++ B`, splits it at the two darts starting at the pinch vertex
(`ClosedWalkFaceColouring.closedChain_split`), and rotates the lobe `C ++ A` back.

* `IsClosedDartWalk.excise`: list form.
* `IsClosedDartWalk.excise_take_drop`: index form.

This is sub-step 3 of the quadrant move (`GreendlingerLeaf.P10FilterMoveExists`,
`p10FM_QuadrantMoveStatement`): once the removed darts are one contiguous stretch of the boundary
cycle, the closed-walk clause is this lemma.  Lane nm-osin94, for nm-gl03d.

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams, residual 10 of the Below
waist).  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

namespace IsClosedDartWalk

universe v

variable {M : CombMap.{v}}

/-- **Excising a pinched stretch, list form.**  If `A ++ B ++ C` is a closed dart walk, `B` and `C`
are nonempty, and the first darts of `B` and `C` start at the same vertex, then `A ++ C` is a closed
dart walk. -/
theorem excise {A B C : List M.Dart} (hw : IsClosedDartWalk M (A ++ B ++ C)) (hB : B ≠ [])
    (hC : C ≠ []) (hpinch : M.vertexOf (B.head hB) = M.vertexOf (C.head hC)) :
    IsClosedDartWalk M (A ++ C) := by
  obtain ⟨b, B', rfl⟩ := List.exists_cons_of_ne_nil hB
  obtain ⟨c, C', rfl⟩ := List.exists_cons_of_ne_nil hC
  have hbc : M.vertexOf b = M.vertexOf c := hpinch
  obtain ⟨-, hcc⟩ := isClosedDartWalk_iff_closedChain.mp hw
  have hrot : ClosedWalkFaceColouring.ClosedChain
      (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) (c :: (C' ++ A) ++ b :: B') := by
    have h := ClosedWalkFaceColouring.closedChain_append_comm (P := A ++ b :: B') (Q := c :: C')
      hcc
    simpa only [List.append_assoc, List.cons_append] using h
  have hlobe := (ClosedWalkFaceColouring.closedChain_split (d := c) (e := b)
    (fun x => by rw [hbc]) hrot).1
  refine isClosedDartWalk_iff_closedChain.mpr
    ⟨List.append_ne_nil_of_right_ne_nil A (List.cons_ne_nil c C'), ?_⟩
  exact ClosedWalkFaceColouring.closedChain_append_comm (P := c :: C') (Q := A)
    (by simpa only [List.cons_append] using hlobe)

/-- **Excising a pinched stretch, index form.**  If the darts at positions `i < j` of a closed dart
walk start at the same vertex, then the walk without the positions `i, …, j - 1` is a closed dart
walk. -/
theorem excise_take_drop {walk : List M.Dart} (hw : IsClosedDartWalk M walk) {i j : ℕ}
    (hij : i < j) (hj : j < walk.length)
    (hpinch : M.vertexOf walk[i] = M.vertexOf walk[j]) :
    IsClosedDartWalk M (walk.take i ++ walk.drop j) := by
  have hdrop : walk.drop j = (walk.drop i).drop (j - i) := by
    rw [List.drop_drop]
    congr 1
    omega
  have hsplit : walk.take i ++ (walk.drop i).take (j - i) ++ walk.drop j = walk := by
    rw [List.append_assoc]
    conv_rhs => rw [← List.take_append_drop i walk]
    congr 1
    rw [hdrop, List.take_append_drop]
  have hBne : (walk.drop i).take (j - i) ≠ [] := by
    intro h
    have h' := congrArg List.length h
    rw [List.length_take, List.length_drop, List.length_nil] at h'
    omega
  have hCne : walk.drop j ≠ [] := by
    intro h
    have h' := congrArg List.length h
    rw [List.length_drop, List.length_nil] at h'
    omega
  have hBhead : ((walk.drop i).take (j - i)).head hBne = walk[i] := by
    rw [List.head_eq_getElem]
    simp only [List.getElem_take, List.getElem_drop, Nat.add_zero]
  have hChead : (walk.drop j).head hCne = walk[j] := by
    rw [List.head_eq_getElem]
    simp only [List.getElem_drop, Nat.add_zero]
  have hw' : IsClosedDartWalk M (walk.take i ++ (walk.drop i).take (j - i) ++ walk.drop j) := by
    rw [hsplit]
    exact hw
  exact excise hw' hBne hCne (by rw [hBhead, hChead]; exact hpinch)

end IsClosedDartWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsClosedDartWalk.excise
#audit_axioms GroupApproximation.GGT.VanKampen.IsClosedDartWalk.excise_take_drop
