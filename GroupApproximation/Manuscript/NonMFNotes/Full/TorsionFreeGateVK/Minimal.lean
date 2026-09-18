import GroupApproximation.GGT.VanKampen.VanKampenMerge
import GroupApproximation.GGT.VanKampen.CombMapEdgeDeletionEuler
import GroupApproximation.Manuscript.NonMFNotes.Full.TorsionFreeGateVK.LetterDisc

/-!
# Minimal letter discs have no mirror pairs

Let `D` be a letter disc with boundary `u` over relators `R` and at most `m + 1` faces, where
`m` is the least number of relator conjugates whose product is `u`.  If a dart `d` separates
two distinct inner faces whose words, read from `d` and from the dart after `opp d`, are
mirror images, then deleting the edge of `d` merges the two faces into one face reading a
freely trivial word.  The planar van Kampen lemma then writes `u` as a product of two relator
conjugates fewer, contradicting minimality (Lyndon–Schupp, Ch. V §2, Lemma 2.1).

* `letterRel`, `listVal_map_letterRel`: free group letters as relative letters;
* `isSignedConjugate_of_mem_symmetrization`;
* `LetterDisc.vanKampenData`: every inner face of a letter disc is a relator face;
* `LetterDisc.mirror_contra`: the mirror condition across two distinct inner faces of a
  minimal letter disc.

Part of thm:torsionfree (non_mf_group_notes.tex), L7 milestone 1, WO NN07a-A.
-/

namespace GroupApproximation.Full.NN07a.VK

open GroupApproximation.SmallCancellationRouter GroupApproximation.GGT.VanKampen
  GroupApproximation.RelatorDefectBudget

universe u

variable {α : Type u}

/-- A free group letter as a relative letter with no subgroup components. -/
def letterRel (c : α × Bool) : GGT.RelLetter (FreeGroup α) Unit :=
  GGT.RelLetter.base (FreeGroup.mk [c])

theorem listVal_map_letterRel (l : List (α × Bool)) :
    GGT.RelLetter.listVal (l.map letterRel) = FreeGroup.mk l := by
  induction l with
  | nil =>
    rw [List.map_nil, GGT.RelLetter.listVal_nil]
    exact FreeGroup.one_eq_mk
  | cons c t ih =>
    rw [List.map_cons, HullSC.RelWord.listVal_cons, ih]
    exact FreeGroup.mul_mk

theorem letterRel_invLetter (c : α × Bool) :
    letterRel (invLetter c) = HullSC.RelWord.inv (letterRel c) := by
  show GGT.RelLetter.base (FreeGroup.mk [invLetter c]) =
    GGT.RelLetter.base (FreeGroup.mk [c])⁻¹
  rw [FreeGroup.inv_mk, invRev_singleton]

/-- A word of the symmetrization is a signed conjugate of a relator. -/
theorem isSignedConjugate_of_mem_symmetrization {R : Set (List (α × Bool))}
    {w : List (α × Bool)} (hw : w ∈ symmetrization R) :
    IsSignedConjugate (FreeGroup.mk '' R) (FreeGroup.mk w) := by
  obtain ⟨r, hr, h | h⟩ := exists_isConj_of_mem_symmetrization hw
  · obtain ⟨c, hc⟩ := isConj_iff.mp h
    exact ⟨c, FreeGroup.mk r, ⟨r, hr, rfl⟩, Or.inl hc.symm⟩
  · obtain ⟨c, hc⟩ := isConj_iff.mp h
    exact ⟨c, FreeGroup.mk r, ⟨r, hr, rfl⟩, Or.inr hc.symm⟩

namespace LetterDisc

variable {R : Set (List (α × Bool))} {u : List (α × Bool)} (D : LetterDisc R u)

/-- The labelling of a letter disc by relative letters. -/
def relLabel (x : D.map.Dart) : GGT.RelLetter (FreeGroup α) Unit := letterRel (D.label x)

theorem listVal_map_relLabel (l : List D.map.Dart) :
    GGT.RelLetter.listVal (l.map D.relLabel) = FreeGroup.mk (l.map D.label) := by
  have e : l.map D.relLabel = (l.map D.label).map letterRel :=
    (List.map_map (g := letterRel) (f := D.label) (l := l)).symm
  rw [e]
  exact listVal_map_letterRel _

theorem relLabel_alpha (x : D.map.Dart) :
    D.relLabel (D.map.alpha x) = HullSC.RelWord.inv (D.relLabel x) := by
  show letterRel (D.label (D.map.alpha x)) = _
  rw [D.label_alpha]
  exact letterRel_invLetter _

section Classical

open scoped Classical

/-- **The van Kampen data of a letter disc**: every inner face is a relator face. -/
noncomputable def vanKampenData : VanKampenData (FreeGroup.mk '' R) D.map D.relLabel where
  relFaces := Finset.univ.erase (D.map.faceOf D.base)
  outer := D.outer
  outer_cycle := D.outer_cycle
  outer_not_mem := Finset.notMem_erase _ _
  rel := fun l hl hmem => by
    rw [D.listVal_map_relLabel]
    exact isSignedConjugate_of_mem_symmetrization (D.face_word l hl (Finset.mem_erase.mp hmem).1)
  triv := fun _ _ hne hnot => (hnot (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)).elim

theorem mem_vanKampenData_relFaces (f : D.map.Face) :
    f ∈ D.vanKampenData.relFaces ↔ f ≠ D.map.faceOf D.base :=
  Finset.mem_erase.trans (and_iff_left (Finset.mem_univ f))

end Classical

/-- **Minimal letter discs have no mirror pairs across two distinct inner faces.** -/
theorem mirror_contra {m : ℕ}
    (hmin : ∀ k < m, ¬ IsRelatorProduct (FreeGroup.mk '' R) k (FreeGroup.mk u))
    (hcount : D.map.faceCount ≤ m + 1) (d : D.map.Dart)
    (hd : ¬ D.toLabelledMap.OnFace D.base d)
    (hod : ¬ D.toLabelledMap.OnFace D.base (D.toLabelledMap.opp d))
    (hs : ¬ D.toLabelledMap.OnFace d (D.toLabelledMap.next (D.toLabelledMap.opp d))) :
    D.toLabelledMap.wordFrom d ≠
      FreeGroup.invRev
        (D.toLabelledMap.wordFrom (D.toLabelledMap.next (D.toLabelledMap.opp d))) := by
  classical
  intro hmirror
  -- the two faces, enumerated from the edge of `d`
  have hface : D.map.faceOf d ≠ D.map.faceOf (D.map.alpha d) := by
    intro h
    apply hs
    refine (D.onFace_iff _ _).mpr ?_
    exact h.trans (D.map.faceOf_facePerm (D.map.alpha d)).symm
  obtain ⟨l₁, hl₁, hh₁⟩ := D.map.exists_isFaceCycle_head d
  obtain ⟨l₂, hl₂, hh₂⟩ := D.map.exists_isFaceCycle_head (D.map.alpha d)
  have e₁ : l₁ = d :: l₁.tail := by
    rw [← hh₁]
    exact (List.cons_head_tail hl₁.ne_nil).symm
  have e₂ : l₂ = D.map.alpha d :: l₂.tail := by
    rw [← hh₂]
    exact (List.cons_head_tail hl₂.ne_nil).symm
  obtain ⟨C⟩ : Nonempty (EdgeDeletion.MergeCycles D.map d) :=
    ⟨⟨l₁.tail, l₂.tail, (congrArg D.map.IsFaceCycle e₁).mp hl₁,
      (congrArg D.map.IsFaceCycle e₂).mp hl₂, hface⟩⟩
  have hOa : D.map.faceOf d ≠ D.map.faceOf D.base := fun h =>
    hd ((D.onFace_iff _ _).mpr h.symm)
  have hOg : D.map.faceOf (D.map.alpha d) ≠ D.map.faceOf D.base := fun h =>
    hod ((D.onFace_iff _ _).mpr h.symm)
  -- the face words
  have hw₁ : D.toLabelledMap.wordFrom d = D.label d :: C.xs.map D.label :=
    D.wordFrom_head C.cycO
  have hw₂ : D.toLabelledMap.wordFrom (D.map.alpha d) =
      invLetter (D.label d) :: C.ys.map D.label := by
    rw [← D.label_alpha d]
    exact D.wordFrom_head C.cycG
  have h1 : 1 ≤ D.toLabelledMap.flen (D.map.alpha d) := D.toLabelledMap.flen_pos _
  have hrun1 : D.toLabelledMap.run (D.map.alpha d) 1 = [D.label (D.map.alpha d)] := rfl
  have hsplit := wordFrom_split D.toLabelledMap (D.map.alpha d) h1
  have hrot := wordFrom_iterate_split D.toLabelledMap (D.map.alpha d) h1
  rw [hw₂, hrun1, List.singleton_append, D.label_alpha] at hsplit
  have hY := (List.cons.inj hsplit).2
  rw [hrun1, D.label_alpha, ← hY] at hrot
  have hw₃ : D.toLabelledMap.wordFrom (D.toLabelledMap.next (D.toLabelledMap.opp d)) =
      C.ys.map D.label ++ [invLetter (D.label d)] := hrot
  rw [hw₁, hw₃, FreeGroup.invRev_append, invRev_singleton, invLetter_invLetter,
    List.singleton_append] at hmirror
  have hX : C.xs.map D.label = FreeGroup.invRev (C.ys.map D.label) := (List.cons.inj hmirror).2
  have hval : FreeGroup.mk ((C.xs ++ C.ys).map D.label) = 1 := by
    rw [List.map_append, hX, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk, inv_mul_cancel]
  by_cases hne : C.xs ++ C.ys = []
  · -- both faces have length one: the map is a single edge and has no outer face
    have hxs : C.xs = [] := (List.append_eq_nil_iff.mp hne).1
    have hys : C.ys = [] := (List.append_eq_nil_iff.mp hne).2
    have hfa : D.map.facePerm d = d := by
      have h := C.facePerm_getD_last_xs
      rw [hxs] at h
      exact h
    have hfαa : D.map.facePerm (D.map.alpha d) = D.map.alpha d := by
      have h := C.facePerm_getD_last_ys
      rw [hys] at h
      exact h
    have hσa : D.map.sigma d = D.map.alpha d := by
      rw [D.map.sigma_eq_facePerm_alpha, hfαa]
    have hσαa : D.map.sigma (D.map.alpha d) = d := by
      rw [D.map.sigma_eq_facePerm_alpha, D.map.alpha_involutive, hfa]
    rcases D.map.dart_eq_or_alpha_of_swapped_endpoints D.planar.1 d hσa hσαa D.base with h | h
    · exact hOa (congrArg D.map.faceOf h.symm)
    · exact hOg (congrArg D.map.faceOf h.symm)
  -- delete the edge of `d`, merging the two faces into a trivial face
  obtain ⟨l, hl⟩ :=
    EdgeDeletion.exists_map_value_eq D.map d (C.xs ++ C.ys) fun x hx => C.avoid hx
  have hlne : l ≠ [] := by
    rintro rfl
    exact hne hl.symm
  obtain ⟨V', hV'outer, _, hV'card⟩ := D.vanKampenData.exists_merge C hne hl hlne hOa hOg False
    (fun h => h.elim) (fun _ => (D.listVal_map_relLabel _).trans hval)
  have hrelD : D.map.faceOf d ∈ D.vanKampenData.relFaces :=
    (D.mem_vanKampenData_relFaces _).mpr hOa
  have hrelG : D.map.faceOf (D.map.alpha d) ∈ D.vanKampenData.relFaces :=
    (D.mem_vanKampenData_relFaces _).mpr hOg
  have hcard : V'.relFaces.card + 2 = D.vanKampenData.relFaces.card := by
    simp only [if_pos hrelD, if_pos hrelG, if_neg not_false] at hV'card
    omega
  have hlt : D.vanKampenData.relFaces.card < Fintype.card D.map.Face :=
    Finset.card_lt_univ_of_notMem D.vanKampenData.outer_not_mem
  have hc : Nat.card D.map.Face ≤ m + 1 := hcount
  have hc' : Nat.card D.map.Face = Fintype.card D.map.Face := Nat.card_eq_fintype_card
  have hN := EdgeDeletion.planar_of_neFace D.map d D.planar (l.head hlne) C.face_ne
  have hprod := V'.isRelatorProduct hN (fun e => by
    show D.relLabel (EdgeDeletion.value D.map d (EdgeDeletion.alpha D.map d e)) = _
    rw [EdgeDeletion.alpha_val, D.relLabel_alpha])
  have hmapO : V'.outer.map (fun e => D.relLabel (EdgeDeletion.value D.map d e)) =
      D.outer.map D.relLabel :=
    (List.map_map (g := D.relLabel) (f := EdgeDeletion.value D.map d) (l := V'.outer)).symm.trans
      (congrArg (List.map D.relLabel) hV'outer)
  have hvalO : GGT.RelLetter.listVal
      (V'.outer.map (fun e => D.relLabel (EdgeDeletion.value D.map d e))) = FreeGroup.mk u :=
    (congrArg GGT.RelLetter.listVal hmapO).trans
      ((D.listVal_map_relLabel D.outer).trans (congrArg FreeGroup.mk D.outer_word))
  exact hmin V'.relFaces.card (by omega)
    ((congrArg (IsRelatorProduct (FreeGroup.mk '' R) V'.relFaces.card) hvalO).mp hprod)

end LetterDisc

end GroupApproximation.Full.NN07a.VK
