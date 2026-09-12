import GroupApproximation.GGT.VanKampen.DiscTransport
import GroupApproximation.GGT.VanKampen.FoldTransport
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# Folding a cancelling pair of exterior darts in a disc diagram

Let the exterior traversal of a disc diagram be `s ++ d :: e :: t`, where `e` reads the
formal inverse of the letter of `d`, and let the pair be foldable (`FoldMap.IsFoldable`:
not a spur, distinct ends).  Folding the pair (`FoldMap`) keeps all faces, so the
relator cells transport (`DiscTransport`).  The new exterior word is the old one with
the pair removed.

* `FoldMap.isFaceCycle_of_foldList`: every face cycle transports, in all four cases.
* `FoldDiagram.transport`, `FoldDiagram.diagram`: the folded disc diagram.
* `FoldDiagram.outerWord_eq`, `FoldDiagram.rCellCount_eq`, `FoldDiagram.cover`.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

namespace FoldMap

variable {M : CombMap.{v}} [DecidableEq M.Dart] {p d e : M.Dart}

/-- **Face cycles transport across a fold**, whatever the face. -/
theorem isFaceCycle_of_foldList (h : IsFoldable M p d e) {B : List M.Dart}
    (hB : M.IsFaceCycle B) {l' : List (EdgeDeletion.Dart (joined M p e) e)}
    (hl' : l'.map (EdgeDeletion.value (joined M p e) e) = foldList M d e B) :
    (toCombMap M p e).IsFaceCycle l' := by
  -- transfer from a face cycle `R` of the same face whose transport is known
  have transfer : ∀ {R : List M.Dart} (hR : M.IsFaceCycle R),
      M.faceOf (R.head hR.ne_nil) = M.faceOf (B.head hB.ne_nil) →
      (∀ {l₀ : List (EdgeDeletion.Dart (joined M p e) e)},
        l₀.map (EdgeDeletion.value (joined M p e) e) = foldList M d e R →
          (toCombMap M p e).IsFaceCycle l₀) →
      (toCombMap M p e).IsFaceCycle l' := by
    intro R hR hface hRcyc
    obtain ⟨k, _, hrot⟩ := hR.exists_rotate_eq hB hface
    obtain ⟨j, hj⟩ := foldList_rotate (M := M) (d := d) (e := e) R k
    obtain ⟨l₀, hl₀⟩ := exists_lift_foldList h R
    rw [hrot] at hj
    exact isFaceCycle_of_rotate_lift (hRcyc hl₀) hl₀ (hl'.trans hj)
  by_cases hd : M.faceOf (B.head hB.ne_nil) = M.faceOf d
  · have hdB : d ∈ B := (hB.mem_iff d).mpr hd.symm
    obtain ⟨k, rest0, _, hrot⟩ := hB.exists_rotate_cons hdB
    have hR0 : M.IsFaceCycle (d :: rest0) := by
      have := hB.rotate k
      rwa [hrot] at this
    have hform : ∃ rest, rest0 = e :: rest := by
      rcases rest0 with _ | ⟨y, rest⟩
      · have hc : M.facePerm d = d := hR0.closes
        exact absurd (h.next.symm.trans hc) h.ne_next.symm
      · have hchain := hR0.chain
        rw [List.isChain_cons_cons] at hchain
        exact ⟨rest, by rw [← hchain.1, h.next]⟩
    obtain ⟨rest, rfl⟩ := hform
    refine transfer hR0 (by rw [List.head_cons]; exact hd.symm) ?_
    intro l₀ hl₀
    by_cases hαe : M.alpha e ∈ rest
    · obtain ⟨s1, s2, rfl⟩ := List.append_of_mem hαe
      exact isFaceCycle_foldList_pair_alpha h hR0 hl₀
    · exact isFaceCycle_foldList_pair h hR0 hαe hl₀
  · by_cases hαe : M.faceOf (B.head hB.ne_nil) = M.faceOf (M.alpha e)
    · have hαeB : M.alpha e ∈ B := (hB.mem_iff _).mpr hαe.symm
      obtain ⟨k, ys, _, hrot⟩ := hB.exists_rotate_cons hαeB
      have hY : M.IsFaceCycle (M.alpha e :: ys) := by
        have := hB.rotate k
        rwa [hrot] at this
      refine transfer hY (by rw [List.head_cons]; exact hαe.symm) ?_
      intro l₀ hl₀
      exact isFaceCycle_foldList_alpha h hY (fun h' => hd (hαe.trans h')) hl₀
    · exact isFaceCycle_foldList_off h hB hd hαe hl'

end FoldMap

namespace FoldDiagram

open FoldMap

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

section

variable (Delta : DiscDiagram.{u, w, v} W) [DecidableEq Delta.toCombMap.Dart]
  {p d e : Delta.toCombMap.Dart}

/-- The letter of the relabelled dart `alpha e` is the letter of `d`. -/
theorem label_alpha_next (hlabel : Delta.label e = HullSC.RelWord.inv (Delta.label d)) :
    Delta.label (Delta.toCombMap.alpha e) = Delta.label d := by
  rw [Delta.label_alpha, hlabel, HullSC.RelWord.inv_inv_letter]

/-- Transport keeps the letters of a list avoiding the folded pair. -/
theorem map_label_foldList (h : IsFoldable Delta.toCombMap p d e)
    (hlabel : Delta.label e = HullSC.RelWord.inv (Delta.label d)) {l : List Delta.toCombMap.Dart}
    (hd : d ∉ l) (he : e ∉ l) : (foldList Delta.toCombMap d e l).map Delta.label = l.map Delta.label := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      have hd' : d ∉ l := fun hm => hd (List.mem_cons_of_mem x hm)
      have he' : e ∉ l := fun hm => he (List.mem_cons_of_mem x hm)
      have hxd : x ≠ d := fun hx => hd (hx ▸ List.mem_cons_self)
      have hxe : x ≠ e := fun hx => he (hx ▸ List.mem_cons_self)
      by_cases hxα : x = Delta.toCombMap.alpha e
      · subst hxα
        rw [foldList_cons_alpha (fun h' => h.ne_alpha_next h'.symm)
          (Delta.toCombMap.alpha_fixedPointFree e), List.map_cons, List.map_cons, ih hd' he',
          label_alpha_next Delta hlabel]
      · rw [foldList_cons_of_ne hxd hxe hxα, List.map_cons, List.map_cons, ih hd' he']

/-- The labels of the folded map. -/
def foldLabel (x : (FoldMap.toCombMap Delta.toCombMap p e).Dart) : RelLetter G Lambda :=
  Delta.label (EdgeDeletion.value (joined Delta.toCombMap p e) e x)

variable (h : IsFoldable Delta.toCombMap p d e)
  (hlabel : Delta.label e = HullSC.RelWord.inv (Delta.label d))
  {s t : List Delta.toCombMap.Dart}
  (houter : (Delta.faceBoundary Delta.outerFace).darts = s ++ d :: e :: t)

/-- The transported enumeration of an old face. -/
noncomputable def walk (g : Delta.toCombMap.Face) :
    List (FoldMap.toCombMap Delta.toCombMap p e).Dart :=
  Classical.choose (exists_lift_foldList h (Delta.faceBoundary g).darts)

theorem walk_spec (g : Delta.toCombMap.Face) :
    (walk Delta h g).map (EdgeDeletion.value (joined Delta.toCombMap p e) e) =
      foldList Delta.toCombMap d e (Delta.faceBoundary g).darts :=
  Classical.choose_spec (exists_lift_foldList h (Delta.faceBoundary g).darts)

include houter in
theorem faceOf_d : Delta.toCombMap.faceOf d = Delta.outerFace :=
  ((Delta.faceBoundary Delta.outerFace).mem_iff d).mp (by rw [houter]; simp)

include houter in
theorem faceOf_e : Delta.toCombMap.faceOf e = Delta.outerFace :=
  ((Delta.faceBoundary Delta.outerFace).mem_iff e).mp (by rw [houter]; simp)

include houter in
/-- **The fold as a transport of the disc diagram.** -/
noncomputable def transport : DiscTransport Delta where
  map := FoldMap.toCombMap Delta.toCombMap p e
  planar := FoldMap.planar Delta.planar h
  label := foldLabel Delta
  label_alpha := by
    intro x
    show Delta.label (EdgeDeletion.value (joined Delta.toCombMap p e) e
        (EdgeDeletion.alpha (joined Delta.toCombMap p e) e x)) = _
    rw [EdgeDeletion.alpha_val]
    exact Delta.label_alpha _
  walk := walk Delta h
  isFaceCycle g :=
    isFaceCycle_of_foldList h (Delta.faceBoundary g).isFaceCycle (walk_spec Delta h g)
  word := by
    intro g hg
    have hd : d ∉ (Delta.faceBoundary g).darts := fun hm =>
      hg (((Delta.faceBoundary g).mem_iff d).mp hm ▸ faceOf_d Delta houter)
    have he : e ∉ (Delta.faceBoundary g).darts := fun hm =>
      hg (((Delta.faceBoundary g).mem_iff e).mp hm ▸ faceOf_e Delta houter)
    have hmap : (walk Delta h g).map (foldLabel Delta) =
        ((walk Delta h g).map (EdgeDeletion.value (joined Delta.toCombMap p e) e)).map
          Delta.label := by
      rw [List.map_map]
      rfl
    rw [hmap, walk_spec, map_label_foldList Delta h hlabel hd he]
    rfl
  outer_value := by
    have hnd := (Delta.faceBoundary Delta.outerFace).nodup
    rw [houter] at hnd
    have hds : d ∉ s := fun hm =>
      (List.nodup_append.mp hnd).2.2 _ hm _ List.mem_cons_self rfl
    have hes : e ∉ s := fun hm =>
      (List.nodup_append.mp hnd).2.2 _ hm _ (List.mem_cons_of_mem d List.mem_cons_self) rfl
    have hdt : d ∉ t := fun hm =>
      (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 (List.mem_cons_of_mem e hm)
    have het : e ∉ t := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).2).1
    have hmap : (walk Delta h Delta.outerFace).map (foldLabel Delta) =
        ((walk Delta h Delta.outerFace).map
          (EdgeDeletion.value (joined Delta.toCombMap p e) e)).map Delta.label := by
      rw [List.map_map]
      rfl
    rw [hmap, walk_spec, houter, foldList_append, foldList_cons_d, foldList_cons_e,
      List.map_append, map_label_foldList Delta h hlabel hds hes,
      map_label_foldList Delta h hlabel hdt het, DiscDiagram.faceWord, houter, List.map_append,
      List.map_cons, List.map_cons, HullSC.RelWord.listVal_append,
      HullSC.RelWord.listVal_append, HullSC.RelWord.listVal_cons, HullSC.RelWord.listVal_cons,
      hlabel, HullSC.RelWord.val_inv, mul_inv_cancel_left]
  cover := by
    intro x
    have hy1 := EdgeDeletion.value_ne (joined Delta.toCombMap p e) e x
    have hy2 := EdgeDeletion.value_ne_reverse (joined Delta.toCombMap p e) e x
    have hmem : ∀ g, EdgeDeletion.value (joined Delta.toCombMap p e) e x ∈
        foldList Delta.toCombMap d e (Delta.faceBoundary g).darts → x ∈ walk Delta h g := by
      intro g hg
      rw [← walk_spec Delta h g] at hg
      obtain ⟨x', hx', hxx'⟩ := List.mem_map.mp hg
      rwa [EdgeDeletion.value_injective (joined Delta.toCombMap p e) e hxx'] at hx'
    by_cases hyd : EdgeDeletion.value (joined Delta.toCombMap p e) e x = d
    · refine ⟨Delta.toCombMap.faceOf (Delta.toCombMap.alpha e), hmem _ ?_⟩
      rw [hyd]
      refine List.mem_filterMap.mpr ⟨Delta.toCombMap.alpha e,
        ((Delta.faceBoundary _).mem_iff _).mpr rfl, ?_⟩
      simp [foldImage, fun h' : Delta.toCombMap.alpha e = d => h.ne_alpha_next h'.symm,
        Delta.toCombMap.alpha_fixedPointFree e]
    · refine ⟨Delta.toCombMap.faceOf (EdgeDeletion.value (joined Delta.toCombMap p e) e x),
        hmem _ ?_⟩
      refine List.mem_filterMap.mpr ⟨_, ((Delta.faceBoundary _).mem_iff _).mpr rfl, ?_⟩
      simp only [foldImage, hyd, false_or, if_neg hy1, if_neg hy2]
  faceCount_eq := FoldMap.faceCount_eq Delta.planar h

/-- **The folded disc diagram.** -/
noncomputable def diagram : DiscDiagram.{u, w, v} W :=
  (transport Delta h hlabel houter).diagram

/-- The exterior traversal of the folded diagram reads the old one without the pair. -/
theorem outerWord_eq :
    (diagram Delta h hlabel houter).faceWord (diagram Delta h hlabel houter).outerFace =
      s.map Delta.label ++ t.map Delta.label := by
  have hnd := (Delta.faceBoundary Delta.outerFace).nodup
  rw [houter] at hnd
  have hds : d ∉ s := fun hm =>
    (List.nodup_append.mp hnd).2.2 _ hm _ List.mem_cons_self rfl
  have hes : e ∉ s := fun hm =>
    (List.nodup_append.mp hnd).2.2 _ hm _ (List.mem_cons_of_mem d List.mem_cons_self) rfl
  have hdt : d ∉ t := fun hm =>
    (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 (List.mem_cons_of_mem e hm)
  have het : e ∉ t := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).2).1
  rw [diagram, DiscTransport.diagram_outerWord]
  have hmap : (walk Delta h Delta.outerFace).map (foldLabel Delta) =
      ((walk Delta h Delta.outerFace).map
        (EdgeDeletion.value (joined Delta.toCombMap p e) e)).map Delta.label := by
    rw [List.map_map]
    rfl
  show (walk Delta h Delta.outerFace).map (foldLabel Delta) = _
  rw [hmap, walk_spec, houter, foldList_append, foldList_cons_d, foldList_cons_e, List.map_append,
    map_label_foldList Delta h hlabel hds hes, map_label_foldList Delta h hlabel hdt het]

/-- **The relator area is unchanged.** -/
theorem rCellCount_eq : (diagram Delta h hlabel houter).rCellCount = Delta.rCellCount :=
  DiscTransport.rCellCount_eq _

/-- **Relator coverage is preserved.** -/
theorem cover (hcover : RelatorCellCover Delta) : RelatorCellCover (diagram Delta h hlabel houter) :=
  DiscTransport.cover_diagram _ hcover

end

end FoldDiagram

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.FoldMap.isFaceCycle_of_foldList
#audit_axioms GroupApproximation.GGT.VanKampen.FoldDiagram.diagram
#audit_axioms GroupApproximation.GGT.VanKampen.FoldDiagram.outerWord_eq
#audit_axioms GroupApproximation.GGT.VanKampen.FoldDiagram.rCellCount_eq
#audit_axioms GroupApproximation.GGT.VanKampen.FoldDiagram.cover
