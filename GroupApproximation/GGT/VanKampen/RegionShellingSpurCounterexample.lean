import GroupApproximation.GGT.VanKampen.FaceSetEarSpurCounterexample
import GroupApproximation.GGT.VanKampen.FaceShelling
import GroupApproximation.Meta.AxiomGuard

/-!
# A face set with a spur has no shelling

`RegionShellingStatement` (`FaceShelling.lean`) asks that the boundary cycle of every face set
with a `FaceSetBoundary` be the last walk of a `FaceShelling`.  The spur map of
`FaceSetEarSpurCounterexample` refutes it.  That map has four darts, face cycles `[0,1,2]` and
`[3]`, the spur `{0,1}` inside the selected face `face 0`, and the boundary cycle `[2]`.

Along a shelling of `{face 0}` every walk avoids the outer dart `3`.  So no attached arc contains
`2`, whose reverse is `3`, and no reversed arc contains `2`, which is the reverse of `3` only;
each step therefore adds exactly one copy of `2`.  A shelling ending at `[2]` has one step, from
the empty walk, and its walk is then the whole face boundary, which contains `0`.

A shelling step replaces an arc by the exposed part of one face and never erases a spur, so
pasting data for a region whose faces carry spurs has to come from `FaceSetWordHomotopy`.
-/

namespace GroupApproximation.GGT.VanKampen.RegionShellingSpurCounterexample

open GroupApproximation.GGT.VanKampen.FaceSetEarSpurCounterexample

/-- The darts of the selected face are the darts other than the outer dart `3`. -/
theorem mem_darts_iff (d : Fin 4) :
    d ∈ (diagram.faceBoundary (face 0)).darts ↔ (d : diagram.toCombMap.Dart) ≠ 3 :=
  ((diagram.faceBoundary (face 0)).mem_iff d).trans
    ((faceOf_eq_face d 0).trans (by fin_cases d <;> decide))

/-- The reverse of a dart is `3` exactly at `2`. -/
theorem alpha_eq_three_iff (d : Fin 4) :
    diagram.toCombMap.alpha d = (3 : diagram.toCombMap.Dart) ↔
      (d : diagram.toCombMap.Dart) = 2 := by
  fin_cases d <;> decide

/-- The reverse of a dart is `2` exactly at `3`. -/
theorem alpha_eq_two_iff (d : Fin 4) :
    diagram.toCombMap.alpha d = (2 : diagram.toCombMap.Dart) ↔
      (d : diagram.toCombMap.Dart) = 3 := by
  fin_cases d <;> decide

/-- Along a shelling of `{face 0}` every walk avoids the outer dart `3` and holds one copy of `2`
for each attached face.  Before the first face the walk is empty, and after exactly one face it
holds `0`. -/
theorem shelling_invariant {l : List diagram.toCombMap.Face}
    {walk : List diagram.toCombMap.Dart}
    (h : Embedded.FaceShelling diagram faces l walk) :
    (∀ d ∈ walk, d ≠ 3) ∧ walk.count 2 = l.length ∧ (l = [] → walk = []) ∧
      (l.length = 1 → (0 : diagram.toCombMap.Dart) ∈ walk) := by
  induction h with
  | empty => simp
  | @step l before arc after exposed f hf k hrot _rest ih =>
    obtain ⟨havoid, hcount, hnil, -⟩ := ih
    have hf0 : f = face 0 := Finset.mem_singleton.mp hf
    subst hf0
    have hrotMem : ∀ d ∈ exposed ++ Embedded.invDarts diagram arc, d ≠ 3 := by
      intro d hd
      rw [← hrot] at hd
      exact (mem_darts_iff d).mp (List.mem_rotate.mp hd)
    have harc2 : (2 : diagram.toCombMap.Dart) ∉ arc := by
      intro h2
      have hmem : diagram.toCombMap.alpha 2 ∈ Embedded.invDarts diagram arc :=
        List.mem_map.mpr ⟨2, List.mem_reverse.mpr h2, rfl⟩
      exact hrotMem _ (List.mem_append_right _ hmem)
        ((alpha_eq_three_iff (2 : diagram.toCombMap.Dart)).mpr (by decide))
    have hinv2 : (2 : diagram.toCombMap.Dart) ∉ Embedded.invDarts diagram arc := by
      intro h2
      obtain ⟨a, ha, hae⟩ := List.mem_map.mp h2
      exact havoid a (List.mem_append_left _ (List.mem_append_right _ (List.mem_reverse.mp ha)))
        ((alpha_eq_two_iff a).mp hae)
    have hone : (exposed ++ Embedded.invDarts diagram arc).count 2 = 1 := by
      rw [← hrot, (List.rotate_perm (diagram.faceBoundary (face 0)).darts k).count_eq]
      exact List.count_eq_one_of_mem (diagram.faceBoundary (face 0)).nodup
        ((mem_darts_iff (2 : diagram.toCombMap.Dart)).mpr (by decide))
    rw [List.count_append, List.count_eq_zero_of_not_mem hinv2] at hone
    rw [List.count_append, List.count_append, List.count_eq_zero_of_not_mem harc2] at hcount
    refine ⟨?_, ?_, fun hl => absurd hl (List.cons_ne_nil _ _), ?_⟩
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · rcases List.mem_append.mp hd with hd | hd
        · exact havoid d (List.mem_append_left _ (List.mem_append_left _ hd))
        · exact hrotMem d (List.mem_append_left _ hd)
      · exact havoid d (List.mem_append_right _ hd)
    · rw [List.count_append, List.count_append, List.length_cons]
      omega
    · intro hl
      cases l with
      | cons _ _ =>
        rw [List.length_cons, List.length_cons] at hl
        omega
      | nil =>
        obtain ⟨hleft, hafter⟩ := List.append_eq_nil_iff.mp (hnil rfl)
        obtain ⟨hbefore, harc⟩ := List.append_eq_nil_iff.mp hleft
        subst hbefore harc hafter
        rw [Embedded.invDarts_nil, List.append_nil] at hrot
        have h0 : (0 : diagram.toCombMap.Dart) ∈
            (diagram.faceBoundary (face 0)).darts.rotate k :=
          List.mem_rotate.mpr ((mem_darts_iff (0 : diagram.toCombMap.Dart)).mpr (by decide))
        rw [hrot] at h0
        simpa using h0

/-- The face set `{face 0}` of the spur map has no shelling of its boundary cycle. -/
theorem no_shelling (l : List diagram.toCombMap.Face) :
    ¬ Embedded.FaceShelling diagram faces l regionBoundary.cycle := by
  intro h
  obtain ⟨-, hcount, -, hzero⟩ := shelling_invariant h
  have hcycle : regionBoundary.cycle = [(2 : diagram.toCombMap.Dart)] := rfl
  rw [hcycle] at hcount hzero
  have hl : l.length = 1 := hcount.symm.trans (by decide)
  exact absurd (hzero hl) (by decide)

/-- The shelling statement is false: a spur inside a selected G-face gives a face set with a
boundary cycle that no shelling reaches. -/
theorem not_regionShellingStatement : ¬ RegionShellingStatement.{0, 0, 0} := by
  intro h
  obtain ⟨l, hl⟩ := h regionBoundary
  exact no_shelling l hl

#audit_closed_axioms not_regionShellingStatement

end GroupApproximation.GGT.VanKampen.RegionShellingSpurCounterexample
