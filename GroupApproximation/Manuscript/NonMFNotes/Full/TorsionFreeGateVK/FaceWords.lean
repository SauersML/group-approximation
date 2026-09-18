import GroupApproximation.Manuscript.NonMFNotes.Full.TorsionFreeGate.LabelledMap
import GroupApproximation.Manuscript.NonMFNotes.Full.TorsionFreeGateVK.Words

/-!
# Face words of a labelled map: rotations, spurs and self-mirrors

Word-level facts about the faces of a `LabelledMap` used in the reduction of minimal
van Kampen diagrams (Lyndon–Schupp, Ch. V §2, Lemma 2.1 and Prop. 2.1):

* `wordFrom_split`, `wordFrom_iterate_split`: reading a face from a later dart rotates
  its word;
* `wordFrom_ne_invRev_iterate`: a face with a reduced word is never its own mirror;
* `eq_of_next_opp_eq`: if every face word is reduced, the only possible spur
  `next (opp d) = d` is at the base dart of the outer face;
* `isReducedAway_of`: reducedness away from the outer face only needs the mirror
  condition across two distinct faces.

Part of thm:torsionfree (non_mf_group_notes.tex), L7 milestone 1, WO NN07a-A.
-/

namespace GroupApproximation.Full.NN07a.VK

open GroupApproximation.SmallCancellationRouter

universe u

variable {α : Type u} (M : LabelledMap α)

theorem run_add_two (x : M.Dart) (j : ℕ) :
    M.run x (j + 2) = M.label x :: M.label (M.next x) :: M.run (M.next (M.next x)) j := rfl

/-- The face word from `d` splits at any index `a ≤ flen d`. -/
theorem wordFrom_split (d : M.Dart) {a : ℕ} (ha : a ≤ M.flen d) :
    M.wordFrom d = M.run d a ++ M.run (M.next^[a] d) (M.flen d - a) :=
  (congrArg (M.run d) (Nat.add_sub_cancel' ha).symm).trans (M.run_add d a _)

/-- Reading a face from a later dart rotates its word. -/
theorem wordFrom_iterate_split (d : M.Dart) {a : ℕ} (ha : a ≤ M.flen d) :
    M.wordFrom (M.next^[a] d) = M.run (M.next^[a] d) (M.flen d - a) ++ M.run d a := by
  have e1 : M.wordFrom (M.next^[a] d) = M.run (M.next^[a] d) ((M.flen d - a) + a) := by
    show M.run _ (M.flen (M.next^[a] d)) = _
    rw [M.flen_iterate d a, Nat.sub_add_cancel ha]
  rw [e1, M.run_add, ← Function.iterate_add_apply, Nat.sub_add_cancel ha, M.iterate_flen]

/-- **A face with a reduced word is never its own mirror.** -/
theorem wordFrom_ne_invRev_iterate (d : M.Dart) (hred : FreeGroup.IsReduced (M.wordFrom d))
    (n : ℕ) : M.wordFrom d ≠ FreeGroup.invRev (M.wordFrom (M.next^[n] d)) := by
  have hlt : n % M.flen d < M.flen d := Nat.mod_lt _ (M.flen_pos d)
  have e : M.next^[n] d = M.next^[n % M.flen d] d := Function.iterate_mod_minimalPeriod_eq.symm
  rw [e, wordFrom_iterate_split M d hlt.le]
  have hsplit := wordFrom_split M d hlt.le
  rw [hsplit] at hred ⊢
  refine ne_invRev_swap hred ?_
  intro h0
  have h1 := congrArg List.length h0
  rw [← hsplit, M.length_wordFrom, List.length_nil] at h1
  exact (M.flen_pos d).ne' h1

/-- **Spurs.**  If the outer face word from `o` and every other face word are reduced, then a
dart `d` with `next (opp d) = d` (a vertex of degree one) is `o`. -/
theorem eq_of_next_opp_eq (o : M.Dart) (hout : FreeGroup.IsReduced (M.wordFrom o))
    (hin : ∀ d, ¬ M.OnFace o d → FreeGroup.IsReduced (M.wordFrom d))
    (d : M.Dart) (hd : M.next (M.opp d) = d) : d = o := by
  by_cases hon : M.OnFace o (M.opp d)
  · obtain ⟨m0, hm0⟩ := hon
    obtain ⟨m, hmlt, hm⟩ : ∃ m, m < M.flen o ∧ M.next^[m] o = M.opp d :=
      ⟨m0 % M.flen o, Nat.mod_lt _ (M.flen_pos o),
        (Function.iterate_mod_minimalPeriod_eq (f := M.next) (x := o) (n := m0)).trans hm0⟩
    have hsucc : M.next^[m + 1] o = d :=
      (Function.iterate_succ_apply' M.next m o).trans (by rw [hm, hd])
    by_cases hlast : m + 1 = M.flen o
    · rw [← hsucc, hlast, M.iterate_flen]
    · exfalso
      have e : M.flen o = m + ((M.flen o - m - 2) + 2) := by omega
      have hsplit : M.wordFrom o = M.run o m ++ M.run (M.next^[m] o) ((M.flen o - m - 2) + 2) :=
        (congrArg (M.run o) e).trans (M.run_add o m _)
      rw [run_add_two, hm, hd, M.label_opp] at hsplit
      rw [hsplit] at hout
      exact not_isReduced_append_inv' (M.run o m) _ (M.label d) hout
  · have hred := hin (M.opp d) hon
    by_cases h1 : M.flen (M.opp d) = 1
    · exfalso
      have e := M.iterate_flen (M.opp d)
      rw [h1] at e
      have e' : M.next (M.opp d) = M.opp d := e
      exact M.opp_ne d (e'.symm.trans hd)
    · exfalso
      have hpos := M.flen_pos (M.opp d)
      obtain ⟨j, hj⟩ : ∃ j, M.flen (M.opp d) = j + 2 := ⟨M.flen (M.opp d) - 2, by omega⟩
      have hw : M.wordFrom (M.opp d) = M.run (M.opp d) (j + 2) := congrArg (M.run (M.opp d)) hj
      rw [run_add_two, hd, M.label_opp] at hw
      rw [hw] at hred
      exact not_isReduced_append_inv' [] _ (M.label d) hred

/-- **Reducedness away from the outer face** reduces to the mirror condition across two
distinct faces, once every inner face word is reduced. -/
theorem isReducedAway_of (o : M.Dart)
    (hin : ∀ d, ¬ M.OnFace o d → FreeGroup.IsReduced (M.wordFrom d))
    (hdist : ∀ d, ¬ M.OnFace o d → ¬ M.OnFace o (M.opp d) → ¬ M.OnFace d (M.next (M.opp d)) →
      M.wordFrom d ≠ FreeGroup.invRev (M.wordFrom (M.next (M.opp d)))) :
    M.IsReducedAway o := by
  intro d hd hod
  by_cases hs : M.OnFace d (M.next (M.opp d))
  · obtain ⟨n, hn⟩ := hs
    rw [← hn]
    exact wordFrom_ne_invRev_iterate M d (hin d hd) n
  · exact hdist d hd hod hs

end GroupApproximation.Full.NN07a.VK
