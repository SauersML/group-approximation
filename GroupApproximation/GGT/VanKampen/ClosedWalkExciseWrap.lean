import GroupApproximation.GGT.VanKampen.ClosedWalkExcise
import GroupApproximation.Meta.AxiomGuard

/-!
# Excising a pinched stretch: the end case and the wrapping case

`ClosedWalkExcise` (lane nm-osin94) removes a stretch `walk[i], …, walk[j - 1]` from a closed dart
walk when `walk[i]` and `walk[j]` start at the same vertex, for `j < walk.length`.  This module
states the pinch as the quadrant move meets it (`GreendlingerLeaf.P10FilterMoveExists`,
`p10FM_QuadrantMoveStatement`; sub-step 3 on nm-gl03d's board): after the last removed dart
`walk[j - 1]` the walk is back at the vertex of the first removed dart `walk[i]`.  With the pinch
in that form:

* `IsClosedDartWalk.excise_take_drop_alpha`: the kept darts `walk.take i ++ walk.drop j` form a
  closed dart walk, including the end case `j = walk.length`, when that list is nonempty;
* `IsClosedDartWalk.middle_of_pinch`: the stretch `(walk.drop i).take (j - i)` is itself a closed
  dart walk.  This is the wrapping case: the removed darts are `walk.drop j ++ walk.take i`, read
  cyclically;
* `IsClosedDartWalk.middle_of_wrapPinch`: the same, with the pinch stated on the wrapping removed
  stretch (after `walk[i - 1]` the walk is at the vertex of `walk[j]`).

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams, residual 10).  It certifies
no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

namespace IsClosedDartWalk

universe v

variable {M : CombMap.{v}}

/-- In a closed dart walk, dart `walk[k - 1]` ends where dart `walk[k]` begins. -/
theorem vertexOf_alpha_getElem_pred {walk : List M.Dart} (hw : IsClosedDartWalk M walk) {k : ℕ}
    (hk0 : 0 < k) (hk : k < walk.length) :
    M.vertexOf (M.alpha (walk[k - 1]'(by omega))) = M.vertexOf walk[k] := by
  obtain ⟨_, hchain, _⟩ := hw
  have h := List.isChain_iff_getElem.mp hchain (k - 1) (by omega)
  have hk1 : k - 1 + 1 = k := by omega
  simpa only [hk1] using h

/-- **Excising a pinched stretch, the pinch read after its last dart.**  If after `walk[j - 1]`
the walk is back at the vertex of `walk[i]`, with `i < j ≤ walk.length`, then
`walk.take i ++ walk.drop j` is a closed dart walk whenever it is nonempty. -/
theorem excise_take_drop_alpha {walk : List M.Dart} (hw : IsClosedDartWalk M walk) {i j : ℕ}
    (hij : i < j) (hj : j ≤ walk.length)
    (hpinch : M.vertexOf (M.alpha (walk[j - 1]'(by omega))) = M.vertexOf (walk[i]'(by omega)))
    (hne : walk.take i ++ walk.drop j ≠ []) :
    IsClosedDartWalk M (walk.take i ++ walk.drop j) := by
  rcases Nat.lt_or_ge j walk.length with hjl | hjl
  · have hij' : M.vertexOf (walk[i]'(by omega)) = M.vertexOf (walk[j]'hjl) := by
      rw [← hpinch]
      exact vertexOf_alpha_getElem_pred hw (by omega) hjl
    exact excise_take_drop hw hij hjl hij'
  · have hjeq : j = walk.length := by omega
    subst hjeq
    have hi0 : 0 < i := by
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0
        simp at hne
      · exact h0
    have hd : walk.drop walk.length = [] := by simp
    rw [hd, List.append_nil]
    have hclose : M.vertexOf (M.alpha (walk[walk.length - 1]'(by omega))) =
        M.vertexOf (walk[0]'(by omega)) := by
      obtain ⟨hne0, -, hcl⟩ := hw
      rw [List.getLast_eq_getElem, List.head_eq_getElem] at hcl
      exact hcl
    exact hw.take hi0 (by omega) (hclose.symm.trans hpinch)

/-- **The pinched stretch is a closed dart walk (the wrapping case).**  If after `walk[j - 1]` the
walk is back at the vertex of `walk[i]`, with `i < j ≤ walk.length`, then
`(walk.drop i).take (j - i)`, the darts `walk[i], …, walk[j - 1]`, form a closed dart walk. -/
theorem middle_of_pinch {walk : List M.Dart} (hw : IsClosedDartWalk M walk) {i j : ℕ}
    (hij : i < j) (hj : j ≤ walk.length)
    (hpinch : M.vertexOf (M.alpha (walk[j - 1]'(by omega))) = M.vertexOf (walk[i]'(by omega))) :
    IsClosedDartWalk M ((walk.drop i).take (j - i)) := by
  have hdrop : walk.drop j = (walk.drop i).drop (j - i) := by
    rw [List.drop_drop]
    congr 1
    omega
  have hsplit : walk.take i ++ (walk.drop i).take (j - i) ++ walk.drop j = walk := by
    rw [List.append_assoc]
    conv_rhs => rw [← List.take_append_drop i walk]
    congr 1
    rw [hdrop, List.take_append_drop]
  have hlen : ((walk.drop i).take (j - i)).length = j - i := by
    rw [List.length_take, List.length_drop]
    omega
  have hSne : (walk.drop i).take (j - i) ≠ [] := by
    intro h
    have h' := congrArg List.length h
    rw [hlen, List.length_nil] at h'
    omega
  have hShead : ((walk.drop i).take (j - i)).head hSne = walk[i]'(by omega) := by
    rw [List.head_eq_getElem]
    simp only [List.getElem_take, List.getElem_drop, Nat.add_zero]
  have hSlast : ((walk.drop i).take (j - i)).getLast hSne = walk[j - 1]'(by omega) := by
    rw [List.getLast_eq_getElem]
    have hidx : i + (j - i - 1) = j - 1 := by omega
    simp only [List.getElem_take, List.getElem_drop, hlen, hidx]
  have hw' : IsClosedDartWalk M (walk.take i ++ (walk.drop i).take (j - i) ++ walk.drop j) := by
    rw [hsplit]
    exact hw
  obtain ⟨-, hcc⟩ := isClosedDartWalk_iff_closedChain.mp hw'
  rw [List.append_assoc] at hcc
  have hrot := ClosedWalkFaceColouring.closedChain_append_comm hcc
  rw [List.append_assoc] at hrot
  obtain ⟨hcS, -⟩ := hrot
  refine isClosedDartWalk_iff_closedChain.mpr
    ⟨hSne, (ClosedWalkFaceColouring.closedChain_iff hSne).mpr
      ⟨(List.isChain_append.mp hcS).1, ?_⟩⟩
  rw [hSlast, hShead]
  exact hpinch

/-- **The wrapping case, with the pinch on the removed stretch.**  The removed darts are
`walk.drop j ++ walk.take i`, read cyclically.  If after their last dart `walk[i - 1]` the walk is
back at the vertex of their first dart `walk[j]`, with `0 < i < j < walk.length`, then the kept
darts `(walk.drop i).take (j - i)` form a closed dart walk. -/
theorem middle_of_wrapPinch {walk : List M.Dart} (hw : IsClosedDartWalk M walk) {i j : ℕ}
    (hi0 : 0 < i) (hij : i < j) (hjl : j < walk.length)
    (hwrap : M.vertexOf (M.alpha (walk[i - 1]'(by omega))) = M.vertexOf (walk[j]'hjl)) :
    IsClosedDartWalk M ((walk.drop i).take (j - i)) := by
  refine middle_of_pinch hw hij hjl.le ?_
  rw [vertexOf_alpha_getElem_pred hw (by omega) hjl, ← hwrap,
    vertexOf_alpha_getElem_pred hw hi0 (by omega)]

end IsClosedDartWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsClosedDartWalk.vertexOf_alpha_getElem_pred
#audit_axioms GroupApproximation.GGT.VanKampen.IsClosedDartWalk.excise_take_drop_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.IsClosedDartWalk.middle_of_pinch
#audit_axioms GroupApproximation.GGT.VanKampen.IsClosedDartWalk.middle_of_wrapPinch
