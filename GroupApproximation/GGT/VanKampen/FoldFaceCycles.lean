import GroupApproximation.GGT.VanKampen.FoldMap
import GroupApproximation.GGT.VanKampen.EdgeDeletionFaceCycles
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# Face cycles of a folded map

Folding the consecutive darts `d e` (`FoldMap`) first joins the two ends of the pair.
In the joined map every face avoiding `p` and `e` is unchanged
(`joined_isFaceCycle_of_avoid`), and the face through the pair, enumerated as
`d :: e :: rest`, splits into the digon `[e, d]` (`joined_isFaceCycle_digon`) and
`rest` (`joined_isFaceCycle_rest`).

Deleting the edge of `e` then merges the digon with the face of `alpha e`
(`mergeCycles`), so with `alpha e :: ys` enumerating that face, the folded map has
the face cycle `d :: ys` (`isFaceCycle_merged`): `d` takes the place of `alpha e`.
Every face off the pair face and off the face of `alpha e` keeps its cycle
(`isFaceCycle_of_off`), and so does `rest` when it avoids `alpha e`
(`isFaceCycle_rest`).
-/

namespace GroupApproximation.GGT.VanKampen.FoldMap

open Equiv

universe u

variable {M : CombMap.{u}} [DecidableEq M.Dart] {p d e : M.Dart}

/-- A face cycle avoiding `p` and `e` is a face cycle of the joined map. -/
theorem joined_isFaceCycle_of_avoid {l : List M.Dart} (hl : M.IsFaceCycle l)
    (hp : p ∉ l) (he : e ∉ l) : (joined M p e).IsFaceCycle l := by
  have hkey : ∀ x ∈ l, (joined M p e).facePerm x = M.facePerm x := by
    intro x hx
    rw [joined_facePerm_apply, Equiv.swap_apply_of_ne_of_ne (fun h => hp (h ▸ hx))
      (fun h => he (h ▸ hx))]
  refine ⟨hl.ne_nil, hl.nodup, hl.chain.imp_of_mem_imp fun x y hx _ hxy => (hkey x hx).trans hxy,
    ?_⟩
  rw [hkey _ (List.getLast_mem hl.ne_nil)]
  exact hl.closes

/-- **The pair becomes a digon** in the joined map. -/
theorem joined_isFaceCycle_digon (h : IsFoldable M p d e) :
    (joined M p e).IsFaceCycle [e, d] := by
  refine ⟨List.cons_ne_nil _ _, ?_, ?_, ?_⟩
  · exact List.nodup_cons.mpr
      ⟨fun hmem => h.ne_next (List.mem_singleton.mp hmem).symm, List.nodup_singleton d⟩
  · exact List.isChain_cons_cons.mpr ⟨joined_facePerm_next h, List.IsChain.singleton _⟩
  · exact joined_facePerm_self h

/-- **The rest of the pair face.**  If `d :: e :: rest` enumerates the face of the
pair, then `rest` is a face cycle of the joined map. -/
theorem joined_isFaceCycle_rest (h : IsFoldable M p d e) {rest : List M.Dart}
    (hl : M.IsFaceCycle (d :: e :: rest)) : (joined M p e).IsFaceCycle rest := by
  have hnd := hl.nodup
  have hd_notin : d ∉ rest :=
    fun hmem => (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem e hmem)
  have he_notin : e ∉ rest := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
  have hrest_ne : rest ≠ [] := by
    rintro rfl
    have hc : M.facePerm e = d := hl.closes
    exact h.prev_ne_next (M.facePerm.injective (h.prev.trans hc.symm))
  have hlast : (d :: e :: rest).getLast hl.ne_nil = rest.getLast hrest_ne := by
    rw [List.getLast_cons_cons, List.getLast_cons hrest_ne]
  have hp_last : rest.getLast hrest_ne = p := by
    apply M.facePerm.injective
    rw [h.prev, ← hlast]
    exact hl.closes
  have hchain := hl.chain
  rw [List.isChain_cons_cons, List.isChain_cons] at hchain
  obtain ⟨_, hhead, hrest_chain⟩ := hchain
  have hstep : ∀ x ∈ rest, ∀ y ∈ rest, M.facePerm x = y → (joined M p e).facePerm x = y := by
    intro x hx y hy hxy
    have hxp : x ≠ p := by
      rintro rfl
      exact hd_notin (by rw [← h.prev, hxy]; exact hy)
    have hxe : x ≠ e := fun hxe => he_notin (hxe ▸ hx)
    rw [joined_facePerm_apply, Equiv.swap_apply_of_ne_of_ne hxp hxe, hxy]
  refine ⟨hrest_ne, (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2,
    hrest_chain.imp_of_mem_imp fun x y hx hy hxy => hstep x hx y hy hxy, ?_⟩
  rw [hp_last, joined_facePerm_prev]
  obtain ⟨y, t, rfl⟩ := List.exists_cons_of_ne_nil hrest_ne
  exact hhead y rfl

/-- **The deletion data of the fold.**  In the joined map the edge of `e` separates
the digon `[e, d]` from the face of `alpha e`. -/
def mergeCycles (h : IsFoldable M p d e) {ys : List M.Dart}
    (hys : (joined M p e).IsFaceCycle (M.alpha e :: ys)) :
    EdgeDeletion.MergeCycles (joined M p e) e where
  xs := [d]
  ys := ys
  cycO := joined_isFaceCycle_digon h
  cycG := hys
  face_ne := joined_faceOf_ne h

/-- **The merged face.**  With `alpha e :: ys` enumerating the face of `alpha e` in
the joined map, the lift of `d :: ys` is a face cycle of the folded map. -/
theorem isFaceCycle_merged (h : IsFoldable M p d e) {ys : List M.Dart}
    (hys : (joined M p e).IsFaceCycle (M.alpha e :: ys))
    {l : List (EdgeDeletion.Dart (joined M p e) e)}
    (hl : l.map (EdgeDeletion.value (joined M p e) e) = d :: ys) :
    (toCombMap M p e).IsFaceCycle l :=
  (mergeCycles h hys).isFaceCycle_lift (List.cons_ne_nil _ _) hl

/-- The dart before `d` lies on the face of `d`. -/
theorem IsFoldable.faceOf_prev (h : IsFoldable M p d e) : M.faceOf p = M.faceOf d := by
  rw [← M.faceOf_facePerm p, h.prev]

/-- The dart after `d` lies on the face of `d`. -/
theorem IsFoldable.faceOf_next (h : IsFoldable M p d e) : M.faceOf e = M.faceOf d := by
  rw [← h.next, M.faceOf_facePerm]

/-- **Every other face keeps its cycle.**  A face cycle off the face of the pair and
off the face of `alpha e` lifts to a face cycle of the folded map. -/
theorem isFaceCycle_of_off (h : IsFoldable M p d e) {L : List M.Dart} (hL : M.IsFaceCycle L)
    (hoff1 : M.faceOf (L.head hL.ne_nil) ≠ M.faceOf d)
    (hoff2 : M.faceOf (L.head hL.ne_nil) ≠ M.faceOf (M.alpha e))
    {l : List (EdgeDeletion.Dart (joined M p e) e)}
    (hl : l.map (EdgeDeletion.value (joined M p e) e) = L) :
    (toCombMap M p e).IsFaceCycle l := by
  have hface : ∀ x ∈ L, M.faceOf x = M.faceOf (L.head hL.ne_nil) := fun x hx => (hL.mem_iff x).mp hx
  have hne_p : ∀ x ∈ L, x ≠ p := fun x hx hxp =>
    hoff1 ((hface x hx).symm.trans (by rw [hxp]; exact h.faceOf_prev))
  have hne_e : ∀ x ∈ L, x ≠ e := fun x hx hxe =>
    hoff1 ((hface x hx).symm.trans (by rw [hxe]; exact h.faceOf_next))
  have hsucc : ∀ x ∈ L, (joined M p e).facePerm x = M.facePerm x := by
    intro x hx
    rw [joined_facePerm_apply, Equiv.swap_apply_of_ne_of_ne (hne_p x hx) (hne_e x hx)]
  have hnext : ∀ x ∈ L, EdgeDeletion.next (joined M p e) e x = M.facePerm x := by
    intro x hx
    have hf : M.faceOf (M.facePerm x) = M.faceOf (L.head hL.ne_nil) := by
      rw [M.faceOf_facePerm]
      exact hface x hx
    have h1 : (joined M p e).facePerm x ≠ e := by
      rw [hsucc x hx]
      intro hxe
      exact hoff1 (hf.symm.trans (by rw [hxe]; exact h.faceOf_next))
    have h2 : (joined M p e).facePerm x ≠ (joined M p e).alpha e := by
      rw [hsucc x hx, joined_alpha]
      intro hxe
      exact hoff2 (hf.symm.trans (by rw [hxe]))
    rw [EdgeDeletion.next_of_ne_of_ne (joined M p e) e h1 h2, hsucc x hx]
  refine EdgeDeletion.isFaceCycle_of_map_value (joined M p e) e hl hL.ne_nil hL.nodup
    (hL.chain.imp_of_mem_imp fun x y hx _ hxy => (hnext x hx).trans hxy) ?_
  intro u hu v hv
  rw [List.getLast?_eq_some_getLasthL.ne_nil, Option.mem_def, Option.some.injEq] at hu
  rw [List.head?_eq_some_headhL.ne_nil, Option.mem_def, Option.some.injEq] at hv
  subst hu
  subst hv
  rw [hnext _ (List.getLast_mem hL.ne_nil)]
  exact hL.closes

/-- **The rest of the pair face keeps its cycle** when it avoids `alpha e`. -/
theorem isFaceCycle_rest (h : IsFoldable M p d e) {rest : List M.Dart}
    (hl : M.IsFaceCycle (d :: e :: rest)) (hαe : M.alpha e ∉ rest)
    {l : List (EdgeDeletion.Dart (joined M p e) e)}
    (hl' : l.map (EdgeDeletion.value (joined M p e) e) = rest) :
    (toCombMap M p e).IsFaceCycle l := by
  have hJ := joined_isFaceCycle_rest h hl
  have he_notin : e ∉ rest := (List.nodup_cons.mp (List.nodup_cons.mp hl.nodup).2).1
  have hsucc_mem : ∀ x ∈ rest, (joined M p e).facePerm x ∈ rest := by
    intro x hx
    apply (hJ.mem_iff _).mpr
    rw [(joined M p e).faceOf_facePerm]
    exact (hJ.mem_iff x).mp hx
  have hnext : ∀ x ∈ rest, EdgeDeletion.next (joined M p e) e x = (joined M p e).facePerm x := by
    intro x hx
    have h1 : (joined M p e).facePerm x ≠ e := fun hxe => he_notin (hxe ▸ hsucc_mem x hx)
    have h2 : (joined M p e).facePerm x ≠ (joined M p e).alpha e :=
      fun hxe => hαe (hxe ▸ hsucc_mem x hx)
    exact EdgeDeletion.next_of_ne_of_ne (joined M p e) e h1 h2
  refine EdgeDeletion.isFaceCycle_of_map_value (joined M p e) e hl' hJ.ne_nil hJ.nodup
    (hJ.chain.imp_of_mem_imp fun x y hx _ hxy => (hnext x hx).trans hxy) ?_
  intro u hu v hv
  rw [List.getLast?_eq_some_getLasthJ.ne_nil, Option.mem_def, Option.some.injEq] at hu
  rw [List.head?_eq_some_headhJ.ne_nil, Option.mem_def, Option.some.injEq] at hv
  subst hu
  subst hv
  rw [hnext _ (List.getLast_mem hJ.ne_nil)]
  exact hJ.closes

end GroupApproximation.GGT.VanKampen.FoldMap

#audit_axioms GroupApproximation.GGT.VanKampen.FoldMap.joined_isFaceCycle_of_avoid
#audit_axioms GroupApproximation.GGT.VanKampen.FoldMap.joined_isFaceCycle_digon
#audit_axioms GroupApproximation.GGT.VanKampen.FoldMap.joined_isFaceCycle_rest
#audit_axioms GroupApproximation.GGT.VanKampen.FoldMap.isFaceCycle_merged
#audit_axioms GroupApproximation.GGT.VanKampen.FoldMap.isFaceCycle_of_off
#audit_axioms GroupApproximation.GGT.VanKampen.FoldMap.isFaceCycle_rest
