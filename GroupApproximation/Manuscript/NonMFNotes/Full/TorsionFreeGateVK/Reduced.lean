import GroupApproximation.Manuscript.NonMFNotes.Full.TorsionFreeGateVK.Minimal

/-!
# Minimal letter discs are reduced relator maps

A letter disc with boundary `invRev w`, where `w` is reduced, and with at most `m + 1` faces,
where `m` is the least number of relator conjugates whose product is `invRev w`, is a
reduced relator map in the sense of `exists_reducedRelatorMap` (WO NN07a-A):

* it is connected and spherical, its outer face reads `invRev w`, and every other face reads
  a word of the symmetrization (`LetterDisc` API);
* it is reduced away from the outer face (`LetterDisc.mirror_contra`, Lyndon–Schupp, Ch. V
  §2, Lemma 2.1);
* its only spur is at the base dart (`eq_of_next_opp_eq`).

Also `exists_minimal_isRelatorProduct`: the least relator product count of an element of the
normal closure exists.

Part of thm:torsionfree (non_mf_group_notes.tex), L7 milestone 1, WO NN07a-A.
-/

namespace GroupApproximation.Full.NN07a.VK

open GroupApproximation.SmallCancellationRouter GroupApproximation.RelatorDefectBudget

universe u

variable {α : Type u}

/-- **Least relator product count.**  An element of the normal closure of `mk '' R` whose
formal inverse word is `invRev w` is a product of `m` signed relator conjugates for some `m`
admitting no shorter product. -/
theorem exists_minimal_isRelatorProduct {R : Set (List (α × Bool))} {w : List (α × Bool)}
    (hmem : FreeGroup.mk w ∈ Subgroup.normalClosure (FreeGroup.mk '' R)) :
    ∃ m, IsRelatorProduct (FreeGroup.mk '' R) m (FreeGroup.mk (FreeGroup.invRev w)) ∧
      ∀ k < m, ¬ IsRelatorProduct (FreeGroup.mk '' R) k (FreeGroup.mk (FreeGroup.invRev w)) := by
  classical
  have hinv : FreeGroup.mk (FreeGroup.invRev w) ∈ Subgroup.normalClosure (FreeGroup.mk '' R) := by
    rw [← FreeGroup.inv_mk]
    exact Subgroup.inv_mem _ hmem
  have hex : ∃ m, IsRelatorProduct (FreeGroup.mk '' R) m (FreeGroup.mk (FreeGroup.invRev w)) :=
    exists_isRelatorProduct hinv
  exact ⟨Nat.find hex, Nat.find_spec hex, fun _ hk => Nat.find_min hex hk⟩

namespace LetterDisc

/-- **A minimal letter disc is a reduced relator map.** -/
theorem exists_reducedRelatorMap_of_minimal {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) {w : List (α × Bool)}
    (hw : FreeGroup.IsReduced w) {m : ℕ} (D : LetterDisc R (FreeGroup.invRev w))
    (hmin : ∀ k < m,
      ¬ IsRelatorProduct (FreeGroup.mk '' R) k (FreeGroup.mk (FreeGroup.invRev w)))
    (hcount : D.map.faceCount ≤ m + 1) :
    ∃ (M : LabelledMap α) (o : M.Dart), M.IsConnected ∧ M.IsSpherical ∧
      M.wordFrom o = FreeGroup.invRev w ∧
      (∀ d, ¬ M.OnFace o d → M.wordFrom d ∈ SmallCancellationRouter.symmetrization R) ∧
      M.IsReducedAway o ∧ (∀ d, M.next (M.opp d) = d → d = o) := by
  have hout : FreeGroup.IsReduced (D.toLabelledMap.wordFrom D.base) := by
    rw [D.wordFrom_outer]
    exact isReduced_invRev_iff.mpr hw
  have hin : ∀ d, ¬ D.toLabelledMap.OnFace D.base d →
      FreeGroup.IsReduced (D.toLabelledMap.wordFrom d) := fun d hd =>
    (symmetrization_isCyclicallyReduced hR (D.wordFrom_mem_symmetrization d hd)).isReduced
  exact ⟨D.toLabelledMap, D.base, D.isConnected, D.isSpherical, D.wordFrom_outer,
    D.wordFrom_mem_symmetrization,
    isReducedAway_of D.toLabelledMap D.base hin (D.mirror_contra hmin hcount),
    eq_of_next_opp_eq D.toLabelledMap D.base hout hin⟩

end LetterDisc

end GroupApproximation.Full.NN07a.VK
