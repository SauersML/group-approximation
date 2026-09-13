import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchedTwoGonRegion
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# The pinched two-gon pocket is a noncrossing closed walk

A model test for `IsNoncrossingClosedWalk` (`NoncrossingClosedWalkSides.lean`) on the pocket of
`Estimating/OsinPocketPinchedTwoGonRegion.lean`.  The cycle `[5,3,4,6]` of that pocket passes twice
through the pinch vertex `{1,3,6,8}`, so it is not a simple closed walk (`not_isSimpleClosedWalk`).
It is noncrossing:

* no edge is used in both directions, and one rotation step from the reversal of each walk dart
  reaches a walk dart (`1 ↦ 6`, `0 ↦ 4`, `8 ↦ 3`, `9 ↦ 5`), so the walk touches itself at the pinch
  vertex without crossing (`isNoncrossingClosedWalk_pinchCycle`, `pocket_noncrossing_not_simple`);
* the faces on the side of the walk are the two digons (`sideFaces_pinchCycle`,
  `sideFaces_pocket`), so the separation of `NoncrossingClosedWalkSides.lean` recovers the pocket
  face set.

So the noncrossing carrier covers the pinched pocket that `IsSimpleClosedWalk` excludes.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 1636, through Osin's Lemma 9.7(b)); certifies no
printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketPinchedTwoGonModel

/-- One rotation step from the reversal of each dart of the pocket cycle reaches a dart of the
cycle. -/
theorem sigma_alpha_mem_pinchCycle :
    ∀ d ∈ ([5, 3, 4, 6] : List diagram.toCombMap.Dart),
      diagram.toCombMap.sigma (diagram.toCombMap.alpha d) ∈
        ([5, 3, 4, 6] : List diagram.toCombMap.Dart) := by
  decide

/-- **The pocket cycle is a noncrossing closed walk.** -/
theorem isNoncrossingClosedWalk_pinchCycle :
    IsNoncrossingClosedWalk diagram.toCombMap ([5, 3, 4, 6] : List (Fin 10)) where
  ne_nil := List.cons_ne_nil _ _
  nodup := by decide
  chain := List.isChain_cons_cons.mpr ⟨vertexEquiv.injective (by decide),
    List.isChain_cons_cons.mpr ⟨vertexEquiv.injective (by decide),
      List.isChain_cons_cons.mpr ⟨vertexEquiv.injective (by decide),
        List.isChain_singleton _⟩⟩⟩
  closes := vertexEquiv.injective (by decide)
  alpha_not_mem := by decide
  turn_mem d hd := NoncrossingClosedWalkSides.turn_mem_of_first Nat.one_pos
    (by rw [pow_one]; exact sigma_alpha_mem_pinchCycle d hd)
    fun _ hk0 hk1 => absurd hk0 (Nat.not_lt.mpr (Nat.le_of_lt_succ hk1))

theorem pocket_isNoncrossingClosedWalk :
    IsNoncrossingClosedWalk diagram.toCombMap pocket.inner.cycle := by
  rw [pocket_inner_cycle]
  exact isNoncrossingClosedWalk_pinchCycle

/-- **The pinched pocket cycle is noncrossing and not simple.** -/
theorem pocket_noncrossing_not_simple :
    IsNoncrossingClosedWalk diagram.toCombMap pocket.inner.cycle ∧
      ¬ IsSimpleClosedWalk diagram.toCombMap pocket.inner.cycle :=
  ⟨pocket_isNoncrossingClosedWalk, not_isSimpleClosedWalk⟩

/-- **The side of the pocket cycle is the pocket face set:** the faces on the side of the walk
`[5,3,4,6]` are the two digons. -/
theorem sideFaces_pinchCycle :
    SimpleClosedWalkSides.sideFaces diagram.toCombMap ([5, 3, 4, 6] : List (Fin 10)) =
      pinchFaces := by
  have hbd : ∀ x : Fin 10, x ∈ ([5, 3, 4, 6] : List (Fin 10)) →
      diagram.toCombMap.faceOf x ∈
          SimpleClosedWalkSides.sideFaces diagram.toCombMap ([5, 3, 4, 6] : List (Fin 10)) ∧
        diagram.toCombMap.faceOf (diagram.toCombMap.alpha x) ∉
          SimpleClosedWalkSides.sideFaces diagram.toCombMap ([5, 3, 4, 6] : List (Fin 10)) :=
    fun x hx =>
      (isNoncrossingClosedWalk_pinchCycle.isBoundaryDart_sideFaces_iff diagram.planar x).mpr hx
  have e0 : diagram.toCombMap.faceOf (diagram.toCombMap.alpha (3 : Fin 10)) = face 0 :=
    (faceOf_eq_face _ 0).mpr (by decide)
  have e1 : diagram.toCombMap.faceOf (3 : Fin 10) = face 1 :=
    (faceOf_eq_face _ 1).mpr (by decide)
  have e2 : diagram.toCombMap.faceOf (5 : Fin 10) = face 2 :=
    (faceOf_eq_face _ 2).mpr (by decide)
  have e3 : diagram.toCombMap.faceOf (diagram.toCombMap.alpha (6 : Fin 10)) = face 3 :=
    (faceOf_eq_face _ 3).mpr (by decide)
  have hnp : ∀ i : Fin 4, i ≠ 1 → i ≠ 2 → face i ∉ pinchFaces := fun i h1 h2 h =>
    (Finset.mem_cons.mp h).elim (fun h => h1 ((face_eq_iff i 1).mp h))
      fun h => h2 ((face_eq_iff i 2).mp (Finset.mem_singleton.mp h))
  have hi : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  ext f
  obtain ⟨i, rfl⟩ : ∃ i, face i = f :=
    ⟨faceEquiv f, faceEquiv.injective (faceEquiv_face (faceEquiv f))⟩
  rcases hi i with rfl | rfl | rfl | rfl
  · refine iff_of_false ?_ (hnp 0 (by decide) (by decide))
    rw [← e0]
    exact (hbd 3 (by decide)).2
  · refine iff_of_true ?_ (Finset.mem_cons.mpr (Or.inl rfl))
    rw [← e1]
    exact (hbd 3 (by decide)).1
  · refine iff_of_true ?_ (Finset.mem_cons.mpr (Or.inr (Finset.mem_singleton_self _)))
    rw [← e2]
    exact (hbd 5 (by decide)).1
  · refine iff_of_false ?_ (hnp 3 (by decide) (by decide))
    rw [← e3]
    exact (hbd 6 (by decide)).2

theorem sideFaces_pocket :
    SimpleClosedWalkSides.sideFaces diagram.toCombMap pocket.inner.cycle = pocket.faces := by
  rw [pocket_inner_cycle, pocket_faces]
  exact sideFaces_pinchCycle

#audit_axioms sigma_alpha_mem_pinchCycle
#audit_closed_axioms isNoncrossingClosedWalk_pinchCycle
#audit_closed_axioms pocket_noncrossing_not_simple
#audit_closed_axioms sideFaces_pinchCycle
#audit_closed_axioms sideFaces_pocket

end GroupApproximation.GGT.VanKampen.OsinPocketPinchedTwoGonModel
