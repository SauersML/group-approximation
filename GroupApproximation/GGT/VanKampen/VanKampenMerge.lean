import GroupApproximation.GGT.VanKampen.PlanarVanKampen
import GroupApproximation.Meta.AxiomGuard

/-!
# Merging two inner faces of a van Kampen map

`VanKampenData R M label` bundles the hypotheses of the planar van Kampen lemma on a
map: an outer face cycle, a set of relator faces not containing the outer face, every
relator face reading a signed conjugate of a relator and every other inner face
reading a freely trivial word.  `VanKampenData.isRelatorProduct` is the lemma itself
(`isRelatorProduct_of_planar`).

Surgeries that remove a cancelling pair of relator cells do not delete an edge on the
outer face; they merge two inner faces.  `VanKampenData.exists_merge` transports the
data across the deletion of an edge between two distinct inner faces
(`EdgeDeletion.MergeCycles`): the merged face is declared a relator face or a trivial
face, every other face keeps its status, and the relator count changes exactly by the
statuses of the two merged faces and of the merged one.

* `EdgeDeletion.isFaceCycle_of_avoid`: a face cycle that never meets or steps onto the
  deleted edge lifts to the deleted map.
* `VanKampenData.exists_merge`.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv HullSC RelatorDefectBudget

universe u w v

/-- **A face cycle avoiding the deleted edge lifts** to a face cycle of the deleted
map. -/
theorem EdgeDeletion.isFaceCycle_of_avoid {M : CombMap.{v}} [DecidableEq M.Dart] {a : M.Dart}
    {L : List M.Dart} (hL : M.IsFaceCycle L)
    (havoid : ∀ x ∈ L, x ≠ a ∧ x ≠ M.alpha a ∧ M.facePerm x ≠ a ∧
      M.facePerm x ≠ M.alpha a)
    {l : List (EdgeDeletion.Dart M a)} (hl : l.map (EdgeDeletion.value M a) = L) :
    (EdgeDeletion.toCombMap M a).IsFaceCycle l := by
  refine EdgeDeletion.isFaceCycle_of_map_value M a hl hL.ne_nil hL.nodup ?_ ?_
  · refine hL.chain.imp_of_mem_imp fun x y hx _ h => ?_
    have h' : M.facePerm x = y := h
    show EdgeDeletion.next M a x = y
    rw [EdgeDeletion.next_of_ne_of_ne M a (havoid x hx).2.2.1 (havoid x hx).2.2.2, h']
  · intro u hu v hv
    have hu' : L.getLast? = some u := hu
    have hv' : L.head? = some v := hv
    have hlast : L.getLast hL.ne_nil = u :=
      Option.some.inj ((List.getLast?_eq_some_getLast hL.ne_nil).symm.trans hu')
    have hhead : L.head hL.ne_nil = v :=
      Option.some.inj ((List.head?_eq_some_head hL.ne_nil).symm.trans hv')
    have hmem : u ∈ L := by
      rw [← hlast]
      exact List.getLast_mem hL.ne_nil
    rw [EdgeDeletion.next_of_ne_of_ne M a (havoid u hmem).2.2.1 (havoid u hmem).2.2.2,
      ← hlast, ← hhead]
    exact hL.closes

section Data

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **Van Kampen data** on a combinatorial map: an outer face cycle and a set of relator
faces not containing the outer face, with every relator face reading a signed
conjugate of a relator and every other inner face reading a freely trivial word. -/
structure VanKampenData (R : Set G) (M : CombMap.{v})
    (label : M.Dart → RelLetter G Lambda) where
  /-- The relator faces. -/
  relFaces : Finset M.Face
  /-- A face cycle of the outer face. -/
  outer : List M.Dart
  outer_cycle : M.IsFaceCycle outer
  outer_not_mem : M.faceOf (outer.head outer_cycle.ne_nil) ∉ relFaces
  rel : ∀ (l : List M.Dart) (hl : M.IsFaceCycle l), M.faceOf (l.head hl.ne_nil) ∈ relFaces →
    IsSignedConjugate R (RelLetter.listVal (l.map label))
  triv : ∀ (l : List M.Dart) (hl : M.IsFaceCycle l),
    M.faceOf (l.head hl.ne_nil) ≠ M.faceOf (outer.head outer_cycle.ne_nil) →
    M.faceOf (l.head hl.ne_nil) ∉ relFaces → RelLetter.listVal (l.map label) = 1

/-- **The planar van Kampen lemma** on van Kampen data. -/
theorem VanKampenData.isRelatorProduct {R : Set G} {M : CombMap.{v}} (hM : M.IsPlanar)
    {label : M.Dart → RelLetter G Lambda}
    (hlabel : ∀ d, label (M.alpha d) = RelWord.inv (label d))
    (V : VanKampenData R M label) :
    IsRelatorProduct R V.relFaces.card (RelLetter.listVal (V.outer.map label)) :=
  isRelatorProduct_of_planar R M.dartCount M rfl hM label hlabel V.relFaces V.outer
    V.outer_cycle V.outer_not_mem V.rel V.triv

/-- **Merging two inner faces.**  Deleting an edge between two distinct inner faces
transports van Kampen data: the merged face is a relator face exactly when `P`, every
other face keeps its status, and the outer cycle lifts. -/
theorem VanKampenData.exists_merge {R : Set G} {M : CombMap.{v}} [DecidableEq M.Dart]
    {label : M.Dart → RelLetter G Lambda} (V : VanKampenData R M label) {a : M.Dart}
    (C : EdgeDeletion.MergeCycles M a) (hne : C.xs ++ C.ys ≠ [])
    (hOa : M.faceOf a ≠ M.faceOf (V.outer.head V.outer_cycle.ne_nil))
    (hOg : M.faceOf (M.alpha a) ≠ M.faceOf (V.outer.head V.outer_cycle.ne_nil))
    (P : Prop) [Decidable P]
    (hrelF : P → IsSignedConjugate R (RelLetter.listVal ((C.xs ++ C.ys).map label)))
    (htrivF : ¬ P → RelLetter.listVal ((C.xs ++ C.ys).map label) = 1) :
    ∃ V' : VanKampenData R (EdgeDeletion.toCombMap M a)
        (fun e => label (EdgeDeletion.value M a e)),
      V'.outer.map (EdgeDeletion.value M a) = V.outer ∧
        V'.relFaces.card + (if M.faceOf a ∈ V.relFaces then 1 else 0) +
            (if M.faceOf (M.alpha a) ∈ V.relFaces then 1 else 0) =
          V.relFaces.card + (if P then 1 else 0) := by
  classical
  obtain ⟨l, hl⟩ := EdgeDeletion.exists_map_value_eq M a (C.xs ++ C.ys) fun d hd => C.avoid hd
  have hlne : l ≠ [] := by
    rintro rfl
    exact hne hl.symm
  have hcyc := C.isFaceCycle_lift hne hl
  have hx₀ : l.head hlne ∈ l := List.head_mem hlne
  have hval : RelLetter.listVal (l.map fun e => label (EdgeDeletion.value M a e)) =
      RelLetter.listVal ((C.xs ++ C.ys).map label) := by
    rw [← hl]
    exact congrArg RelLetter.listVal List.map_map.symm
  -- the outer face lifts
  have havoidO : ∀ x ∈ V.outer, x ≠ a ∧ x ≠ M.alpha a ∧ M.facePerm x ≠ a ∧
      M.facePerm x ≠ M.alpha a := by
    intro x hx
    have hfx : M.faceOf x = M.faceOf (V.outer.head V.outer_cycle.ne_nil) :=
      (V.outer_cycle.mem_iff x).mp hx
    have hfpx : M.faceOf (M.facePerm x) = M.faceOf (V.outer.head V.outer_cycle.ne_nil) := by
      rw [M.faceOf_facePerm]
      exact hfx
    refine ⟨fun h => hOa ?_, fun h => hOg ?_, fun h => hOa ?_, fun h => hOg ?_⟩
    · rw [← h]
      exact hfx
    · rw [← h]
      exact hfx
    · rw [← h]
      exact hfpx
    · rw [← h]
      exact hfpx
  obtain ⟨lO, hlO⟩ := EdgeDeletion.exists_map_value_eq M a V.outer fun x hx =>
    ⟨(havoidO x hx).1, (havoidO x hx).2.1⟩
  have hOcyc := EdgeDeletion.isFaceCycle_of_avoid V.outer_cycle havoidO hlO
  have hlOne : lO ≠ [] := hOcyc.ne_nil
  have hheadO : M.faceOf (EdgeDeletion.value M a (lO.head hlOne)) =
      M.faceOf (V.outer.head V.outer_cycle.ne_nil) := by
    have hmem : EdgeDeletion.value M a (lO.head hlOne) ∈ V.outer := by
      rw [← hlO]
      exact List.mem_map.mpr ⟨_, List.head_mem hlOne, rfl⟩
    exact (V.outer_cycle.mem_iff _).mp hmem
  have hOoff : (EdgeDeletion.toCombMap M a).faceOf (lO.head hlOne) ≠
      (EdgeDeletion.toCombMap M a).faceOf (l.head hlne) := by
    intro h
    have hmem : lO.head hlOne ∈ l := (hcyc.mem_iff _).mpr h
    have hv : EdgeDeletion.value M a (lO.head hlOne) ∈ C.xs ++ C.ys := by
      rw [← hl]
      exact List.mem_map.mpr ⟨_, hmem, rfl⟩
    rcases C.faceOf_of_mem_append hv with h' | h'
    · exact hOa (h'.symm.trans hheadO)
    · exact hOg (h'.symm.trans hheadO)
  have hout : ∀ x : EdgeDeletion.Dart M a,
      (EdgeDeletion.toCombMap M a).faceOf x ≠ (EdgeDeletion.toCombMap M a).faceOf (l.head hlne) →
      M.faceOf (EdgeDeletion.value M a (Quotient.out ((EdgeDeletion.toCombMap M a).faceOf x))) =
        M.faceOf (EdgeDeletion.value M a x) := by
    intro x hx
    have hq : (EdgeDeletion.toCombMap M a).faceOf
        (Quotient.out ((EdgeDeletion.toCombMap M a).faceOf x)) =
          (EdgeDeletion.toCombMap M a).faceOf x :=
      Quotient.out_eq _
    exact C.faceOf_value_eq hne hl hx₀ hq (by rw [hq]; exact hx)
  -- the kept relator faces
  obtain ⟨filt, hfilt⟩ : ∃ s : Finset (EdgeDeletion.toCombMap M a).Face, ∀ f,
      f ∈ s ↔ (f ≠ (EdgeDeletion.toCombMap M a).faceOf (l.head hlne) ∧
        M.faceOf (EdgeDeletion.value M a (Quotient.out f)) ∈ V.relFaces) :=
    ⟨Finset.univ.filter fun f => f ≠ (EdgeDeletion.toCombMap M a).faceOf (l.head hlne) ∧
        M.faceOf (EdgeDeletion.value M a (Quotient.out f)) ∈ V.relFaces, fun f => by simp⟩
  have hmemR : ∀ f, f ∈ (if P then insert ((EdgeDeletion.toCombMap M a).faceOf (l.head hlne))
      filt else filt) ↔
        f ∈ filt ∨ (f = (EdgeDeletion.toCombMap M a).faceOf (l.head hlne) ∧ P) := by
    intro f
    by_cases hP : P
    · rw [if_pos hP, Finset.mem_insert]
      tauto
    · rw [if_neg hP]
      tauto
  have hcardFilt : filt.card =
      ((V.relFaces.erase (M.faceOf a)).erase (M.faceOf (M.alpha a))).card := by
    refine Finset.card_nbij (fun f => M.faceOf (EdgeDeletion.value M a (Quotient.out f)))
      ?_ ?_ ?_
    · intro f hf
      obtain ⟨hoff, hin⟩ := (hfilt f).mp hf
      have hq : (EdgeDeletion.toCombMap M a).faceOf (Quotient.out f) = f := Quotient.out_eq f
      have hne' := C.faceOf_value_ne hne hl hx₀ (x := Quotient.out f) (by rw [hq]; exact hoff)
      exact Finset.mem_erase.mpr ⟨hne'.2, Finset.mem_erase.mpr ⟨hne'.1, hin⟩⟩
    · intro f₁ hf₁ f₂ _ heq
      obtain ⟨hoff₁, -⟩ := (hfilt f₁).mp hf₁
      have hq₁ : (EdgeDeletion.toCombMap M a).faceOf (Quotient.out f₁) = f₁ := Quotient.out_eq f₁
      have hq₂ : (EdgeDeletion.toCombMap M a).faceOf (Quotient.out f₂) = f₂ := Quotient.out_eq f₂
      have hN := C.faceOf_eq_of_faceOf_value_eq hne hl hx₀ (by rw [hq₁]; exact hoff₁) heq
      rw [hq₁, hq₂] at hN
      exact hN
    · intro f hf
      obtain ⟨hne_g, hf'⟩ := Finset.mem_erase.mp hf
      obtain ⟨hne_a, hin⟩ := Finset.mem_erase.mp hf'
      obtain ⟨d, rfl⟩ := Quotient.exists_rep f
      obtain ⟨x, hxd, hxoff⟩ := C.exists_value_eq_of_faceOf_ne hne hl hx₀ hne_a hne_g
      refine ⟨(EdgeDeletion.toCombMap M a).faceOf x, (hfilt _).mpr ⟨hxoff, ?_⟩, ?_⟩
      · rw [hout x hxoff, hxd]
        exact hin
      · show M.faceOf (EdgeDeletion.value M a
          (Quotient.out ((EdgeDeletion.toCombMap M a).faceOf x))) = _
        rw [hout x hxoff, hxd]
        rfl
  have hcardErase : ((V.relFaces.erase (M.faceOf a)).erase (M.faceOf (M.alpha a))).card +
      (if M.faceOf a ∈ V.relFaces then 1 else 0) +
        (if M.faceOf (M.alpha a) ∈ V.relFaces then 1 else 0) = V.relFaces.card := by
    by_cases ha' : M.faceOf a ∈ V.relFaces
    · have h1 := Finset.card_erase_add_one ha'
      by_cases hg' : M.faceOf (M.alpha a) ∈ V.relFaces
      · have h2 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨C.face_ne.symm, hg'⟩)
        simp only [if_pos ha', if_pos hg']
        omega
      · have h2 : (V.relFaces.erase (M.faceOf a)).erase (M.faceOf (M.alpha a)) =
            V.relFaces.erase (M.faceOf a) :=
          Finset.erase_eq_of_notMem fun h => hg' (Finset.mem_of_mem_erase h)
        simp only [if_pos ha', if_neg hg', h2]
        omega
    · have h1 : V.relFaces.erase (M.faceOf a) = V.relFaces := Finset.erase_eq_of_notMem ha'
      by_cases hg' : M.faceOf (M.alpha a) ∈ V.relFaces
      · have h2 := Finset.card_erase_add_one hg'
        simp only [if_neg ha', if_pos hg', h1]
        omega
      · have h2 : V.relFaces.erase (M.faceOf (M.alpha a)) = V.relFaces :=
          Finset.erase_eq_of_notMem hg'
        simp only [if_neg ha', if_neg hg', h1, h2, add_zero]
  refine ⟨{
    relFaces := if P then insert ((EdgeDeletion.toCombMap M a).faceOf (l.head hlne)) filt
      else filt
    outer := lO
    outer_cycle := hOcyc
    outer_not_mem := ?_
    rel := ?_
    triv := ?_ }, hlO, ?_⟩
  · intro h
    rcases (hmemR _).mp h with hf | ⟨hf, _⟩
    · obtain ⟨_, hin⟩ := (hfilt _).mp hf
      rw [hout _ hOoff, hheadO] at hin
      exact V.outer_not_mem hin
    · exact hOoff hf
  · intro l' hl' h
    rcases (hmemR _).mp h with hf | ⟨hf, hP⟩
    · obtain ⟨hoff, hin⟩ := (hfilt _).mp hf
      have hM' := C.isFaceCycle_map_value_of_ne hne hl hx₀ hl' hoff
      have hface' : M.faceOf ((l'.map (EdgeDeletion.value M a)).head hM'.ne_nil) ∈
          V.relFaces := by
        rw [List.head_map, ← hout _ hoff]
        exact hin
      have hsc := V.rel _ hM' hface'
      rwa [List.map_map] at hsc
    · obtain ⟨k, hk, hrot⟩ := hcyc.exists_rotate_eq hl' hf.symm
      rw [← hrot, List.map_rotate]
      refine isSignedConjugate_rotate _ (by rw [List.length_map]; exact hk) ?_
      rw [hval]
      exact hrelF hP
  · intro l' hl' hoffO hnot
    by_cases hF : (EdgeDeletion.toCombMap M a).faceOf (l'.head hl'.ne_nil) =
        (EdgeDeletion.toCombMap M a).faceOf (l.head hlne)
    · have hP : ¬ P := fun hP => hnot ((hmemR _).mpr (Or.inr ⟨hF, hP⟩))
      obtain ⟨k, hk, hrot⟩ := hcyc.exists_rotate_eq hl' hF.symm
      rw [← hrot, List.map_rotate]
      refine listVal_rotate_eq_one _ (by rw [List.length_map]; exact hk) ?_
      rw [hval]
      exact htrivF hP
    · have hM' := C.isFaceCycle_map_value_of_ne hne hl hx₀ hl' hF
      have hnotin : M.faceOf ((l'.map (EdgeDeletion.value M a)).head hM'.ne_nil) ∉
          V.relFaces := by
        rw [List.head_map, ← hout _ hF]
        exact fun h => hnot ((hmemR _).mpr (Or.inl ((hfilt _).mpr ⟨hF, h⟩)))
      have hneO : M.faceOf ((l'.map (EdgeDeletion.value M a)).head hM'.ne_nil) ≠
          M.faceOf (V.outer.head V.outer_cycle.ne_nil) := by
        rw [List.head_map, ← hheadO]
        intro h
        exact hoffO (C.faceOf_eq_of_faceOf_value_eq hne hl hx₀ hF h)
      have hone := V.triv _ hM' hneO hnotin
      rwa [List.map_map] at hone
  · have hFnot : (EdgeDeletion.toCombMap M a).faceOf (l.head hlne) ∉ filt :=
      fun h => ((hfilt _).mp h).1 rfl
    generalize (if M.faceOf a ∈ V.relFaces then 1 else 0) = ia at hcardErase ⊢
    generalize (if M.faceOf (M.alpha a) ∈ V.relFaces then 1 else 0) = ig at hcardErase ⊢
    by_cases hP : P
    · simp only [if_pos hP]
      rw [Finset.card_insert_of_notMem hFnot]
      omega
    · simp only [if_neg hP]
      omega

end Data

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.isFaceCycle_of_avoid
#audit_axioms GroupApproximation.GGT.VanKampen.VanKampenData.isRelatorProduct
#audit_axioms GroupApproximation.GGT.VanKampen.VanKampenData.exists_merge
