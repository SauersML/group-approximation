import GroupApproximation.GGT.VanKampen.VanKampenMerge
import GroupApproximation.GGT.VanKampen.CombMapEdgeDeletionEuler
import GroupApproximation.Meta.AxiomGuard

/-!
# Cancelling two relator faces joined through a trivial face

Let a planar van Kampen map have two relator faces `Π` and `Σ` and a trivial face `γ`,
all distinct and inner, with `Π` and `γ` sharing an edge `b₁` and `γ` and `Σ` sharing an
edge `b₂`.  Enumerate them from the shared edges as the face cycles `b₁ :: xs`,
`alpha b₁ :: (us ++ b₂ :: zs)` and `alpha b₂ :: ws`.  Deleting `b₁` merges `Π` and `γ`
into a relator face enumerated by `xs ++ us ++ b₂ :: zs`; deleting `b₂` then merges it with
`Σ` into one face enumerated by `zs ++ xs ++ us ++ ws`.  If that word reads `1`, the outer
face reads a relator product with two factors fewer:
`VanKampenData.isRelatorProduct_sub_two`.  This is the map-level core of Osin's removal of a
cancelling pair of relator cells (O52 at least area).
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv HullSC RelatorDefectBudget

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}

/-- The head of a mapped list. -/
theorem head_eq_of_map_eq {α β : Type*} {f : α → β} {l : List α} {L : List β}
    (h : l.map f = L) (hl : l ≠ []) (hL : L ≠ []) : f (l.head hl) = L.head hL := by
  subst h
  exact (List.head_map hL).symm

/-- **Two relator faces cancelling through a trivial face.** -/
theorem VanKampenData.isRelatorProduct_sub_two {R : Set G} {M : CombMap.{v}}
    [DecidableEq M.Dart] (hM : M.IsPlanar) {label : M.Dart → RelLetter G Lambda}
    (hlabel : ∀ d, label (M.alpha d) = RelWord.inv (label d)) (V : VanKampenData R M label)
    {b₁ b₂ : M.Dart} {xs us zs ws : List M.Dart}
    (cycΠ : M.IsFaceCycle (b₁ :: xs)) (cycγ : M.IsFaceCycle (M.alpha b₁ :: (us ++ b₂ :: zs)))
    (cycΣ : M.IsFaceCycle (M.alpha b₂ :: ws))
    (hΠrel : M.faceOf b₁ ∈ V.relFaces) (hγrel : M.faceOf (M.alpha b₁) ∉ V.relFaces)
    (hΣrel : M.faceOf (M.alpha b₂) ∈ V.relFaces)
    (hΠO : M.faceOf b₁ ≠ M.faceOf (V.outer.head V.outer_cycle.ne_nil))
    (hγO : M.faceOf (M.alpha b₁) ≠ M.faceOf (V.outer.head V.outer_cycle.ne_nil))
    (hΣO : M.faceOf (M.alpha b₂) ≠ M.faceOf (V.outer.head V.outer_cycle.ne_nil))
    (hΠγ : M.faceOf b₁ ≠ M.faceOf (M.alpha b₁))
    (hΣΠ : M.faceOf (M.alpha b₂) ≠ M.faceOf b₁)
    (hΣγ : M.faceOf (M.alpha b₂) ≠ M.faceOf (M.alpha b₁))
    (hval : RelLetter.listVal ((zs ++ xs ++ us ++ ws).map label) = 1) :
    IsRelatorProduct R (V.relFaces.card - 2) (RelLetter.listVal (V.outer.map label)) := by
  classical
  -- the first merge: `Π` and `γ`
  obtain ⟨C₁, hC₁x, hC₁y⟩ : ∃ C : EdgeDeletion.MergeCycles M b₁,
      C.xs = xs ∧ C.ys = us ++ b₂ :: zs := ⟨⟨xs, us ++ b₂ :: zs, cycΠ, cycγ, hΠγ⟩, rfl, rfl⟩
  have hb₂C : b₂ ∈ C₁.xs ++ C₁.ys := by
    rw [hC₁x, hC₁y]
    simp
  have hne₁ : C₁.xs ++ C₁.ys ≠ [] := fun h => by
    rw [h] at hb₂C
    simp at hb₂C
  obtain ⟨l₁, hl₁⟩ := EdgeDeletion.exists_map_value_eq M b₁ (C₁.xs ++ C₁.ys)
    fun d hd => C₁.avoid hd
  have hl₁ne : l₁ ≠ [] := by
    rintro rfl
    exact hne₁ hl₁.symm
  have hcyc₁ := C₁.isFaceCycle_lift hne₁ hl₁
  have hx₀₁ : l₁.head hl₁ne ∈ l₁ := List.head_mem hl₁ne
  have hβ : RelLetter.listVal ((us ++ b₂ :: zs).map label) = (label b₁).val := by
    have htriv := V.triv _ cycγ hγO hγrel
    rw [List.map_cons, RelWord.listVal_cons, hlabel, RelWord.val_inv] at htriv
    have h := congrArg ((label b₁).val * ·) htriv
    simpa using h
  have hrelF₁ : IsSignedConjugate R (RelLetter.listVal ((C₁.xs ++ C₁.ys).map label)) := by
    have hsc := V.rel _ cycΠ hΠrel
    rw [List.map_cons, RelWord.listVal_cons] at hsc
    have hval₁ : RelLetter.listVal ((C₁.xs ++ C₁.ys).map label) =
        ((label b₁).val)⁻¹ * ((label b₁).val * RelLetter.listVal (xs.map label)) *
          ((label b₁).val)⁻¹⁻¹ := by
      rw [hC₁x, hC₁y, List.map_append, RelWord.listVal_append, hβ]
      group
    rw [hval₁]
    exact hsc.conj _
  obtain ⟨V₁, hV₁outer, hV₁mem, hV₁card⟩ := V.exists_merge C₁ hne₁ hl₁ hl₁ne hΠO hγO True
    (fun _ => hrelF₁) (fun h => absurd trivial h)
  have hcard₁ : V₁.relFaces.card = V.relFaces.card := by
    simp only [if_pos hΠrel, if_neg hγrel, if_pos trivial] at hV₁card
    omega
  -- the dart `b₂` survives
  have hb₂avoid := C₁.avoid hb₂C
  obtain ⟨b₂N, hb₂N⟩ : ∃ x : EdgeDeletion.Dart M b₁, EdgeDeletion.value M b₁ x = b₂ :=
    ⟨EdgeDeletion.ofValue M b₁ b₂ hb₂avoid.1 hb₂avoid.2, rfl⟩
  have hvα : EdgeDeletion.value M b₁ ((EdgeDeletion.toCombMap M b₁).alpha b₂N) = M.alpha b₂ := by
    show EdgeDeletion.value M b₁ (EdgeDeletion.alpha M b₁ b₂N) = _
    rw [EdgeDeletion.alpha_val, hb₂N]
  have hmemb₂ : b₂N ∈ l₁ := by
    apply C₁.mem_lift_of_faceOf hl₁
    rw [hb₂N]
    exact C₁.faceOf_of_mem_append hb₂C
  -- the merged face, starting at `b₂`
  have hrotΔ : (C₁.xs ++ C₁.ys).rotate (xs.length + us.length) = b₂ :: (zs ++ xs ++ us) := by
    rw [hC₁x, hC₁y]
    have h := List.rotate_append_length_eq (xs ++ us) (b₂ :: zs)
    rw [List.length_append] at h
    rw [show xs ++ (us ++ b₂ :: zs) = (xs ++ us) ++ (b₂ :: zs) by simp, h]
    simp
  have hl₁rot : (l₁.rotate (xs.length + us.length)).map (EdgeDeletion.value M b₁) =
      b₂ :: (zs ++ xs ++ us) := by
    rw [List.map_rotate, hl₁, hrotΔ]
  have hl₁rne : l₁.rotate (xs.length + us.length) ≠ [] := by
    intro h
    rw [h] at hl₁rot
    simp at hl₁rot
  have hl₁cons : l₁.rotate (xs.length + us.length) =
      b₂N :: (l₁.rotate (xs.length + us.length)).tail := by
    have hhead : (l₁.rotate (xs.length + us.length)).head hl₁rne = b₂N := by
      apply EdgeDeletion.value_injective M b₁
      rw [hb₂N]
      have h := congrArg List.head? hl₁rot
      rw [List.head?_map, List.head?_eq_some_head hl₁rne] at h
      exact Option.some.inj h
    rw [← hhead]
    exact (List.cons_head_tail hl₁rne).symm
  have htail₁ : (l₁.rotate (xs.length + us.length)).tail.map (EdgeDeletion.value M b₁) =
      zs ++ xs ++ us := by
    have h := hl₁rot
    rw [hl₁cons, List.map_cons] at h
    exact (List.cons.inj h).2
  -- the face `Σ` lifts
  have havoidΣ : ∀ x ∈ M.alpha b₂ :: ws, x ≠ b₁ ∧ x ≠ M.alpha b₁ ∧ M.facePerm x ≠ b₁ ∧
      M.facePerm x ≠ M.alpha b₁ := by
    intro x hx
    have hfx : M.faceOf x = M.faceOf (M.alpha b₂) := (cycΣ.mem_iff x).mp hx
    have hfpx : M.faceOf (M.facePerm x) = M.faceOf (M.alpha b₂) := by
      rw [M.faceOf_facePerm]
      exact hfx
    refine ⟨fun h => hΣΠ ?_, fun h => hΣγ ?_, fun h => hΣΠ ?_, fun h => hΣγ ?_⟩
    · rw [← hfx, h]
    · rw [← hfx, h]
    · rw [← hfpx, h]
    · rw [← hfpx, h]
  obtain ⟨lΣ, hlΣ⟩ := EdgeDeletion.exists_map_value_eq M b₁ (M.alpha b₂ :: ws) fun x hx =>
    ⟨(havoidΣ x hx).1, (havoidΣ x hx).2.1⟩
  have hcycΣ := EdgeDeletion.isFaceCycle_of_avoid cycΣ havoidΣ hlΣ
  have hlΣne : lΣ ≠ [] := by
    rintro rfl
    simp at hlΣ
  have hlΣcons : lΣ = (EdgeDeletion.toCombMap M b₁).alpha b₂N :: lΣ.tail := by
    have hhead : lΣ.head hlΣne = (EdgeDeletion.toCombMap M b₁).alpha b₂N := by
      apply EdgeDeletion.value_injective M b₁
      rw [hvα]
      have h := congrArg List.head? hlΣ
      rw [List.head?_map, List.head?_eq_some_head hlΣne] at h
      exact Option.some.inj h
    rw [← hhead]
    exact (List.cons_head_tail hlΣne).symm
  have htailΣ : lΣ.tail.map (EdgeDeletion.value M b₁) = ws := by
    have h := hlΣ
    rw [hlΣcons, List.map_cons] at h
    exact (List.cons.inj h).2
  have hface₂ : (EdgeDeletion.toCombMap M b₁).faceOf b₂N ≠
      (EdgeDeletion.toCombMap M b₁).faceOf ((EdgeDeletion.toCombMap M b₁).alpha b₂N) := by
    intro h
    have hmemα : (EdgeDeletion.toCombMap M b₁).alpha b₂N ∈ l₁ :=
      (hcyc₁.mem_iff _).mpr (h.symm.trans ((hcyc₁.mem_iff _).mp hmemb₂))
    have hv : EdgeDeletion.value M b₁ ((EdgeDeletion.toCombMap M b₁).alpha b₂N) ∈
        C₁.xs ++ C₁.ys := by
      rw [← hl₁]
      exact List.mem_map.mpr ⟨_, hmemα, rfl⟩
    rw [hvα] at hv
    rcases C₁.faceOf_of_mem_append hv with h' | h'
    · exact hΣΠ h'
    · exact hΣγ h'
  obtain ⟨C₂, hC₂x, hC₂y⟩ : ∃ C : EdgeDeletion.MergeCycles (EdgeDeletion.toCombMap M b₁) b₂N,
      C.xs = (l₁.rotate (xs.length + us.length)).tail ∧ C.ys = lΣ.tail :=
    ⟨⟨(l₁.rotate (xs.length + us.length)).tail, lΣ.tail,
      (congrArg (EdgeDeletion.toCombMap M b₁).IsFaceCycle hl₁cons).mp (hcyc₁.rotate _),
      (congrArg (EdgeDeletion.toCombMap M b₁).IsFaceCycle hlΣcons).mp hcycΣ, hface₂⟩, rfl, rfl⟩
  -- the outer face is off both merges
  have hheadO₁ : EdgeDeletion.value M b₁ (V₁.outer.head V₁.outer_cycle.ne_nil) =
      V.outer.head V.outer_cycle.ne_nil :=
    head_eq_of_map_eq hV₁outer V₁.outer_cycle.ne_nil V.outer_cycle.ne_nil
  have hOa₂ : (EdgeDeletion.toCombMap M b₁).faceOf b₂N ≠
      (EdgeDeletion.toCombMap M b₁).faceOf (V₁.outer.head V₁.outer_cycle.ne_nil) := by
    intro h
    have hmemO : V₁.outer.head V₁.outer_cycle.ne_nil ∈ l₁ :=
      (hcyc₁.mem_iff _).mpr (h.symm.trans ((hcyc₁.mem_iff _).mp hmemb₂))
    have hv : EdgeDeletion.value M b₁ (V₁.outer.head V₁.outer_cycle.ne_nil) ∈
        C₁.xs ++ C₁.ys := by
      rw [← hl₁]
      exact List.mem_map.mpr ⟨_, hmemO, rfl⟩
    have hv' := (congrArg (fun z => z ∈ C₁.xs ++ C₁.ys) hheadO₁).mp hv
    rcases C₁.faceOf_of_mem_append hv' with h' | h'
    · exact hΠO h'.symm
    · exact hγO h'.symm
  have hoffα : (EdgeDeletion.toCombMap M b₁).faceOf ((EdgeDeletion.toCombMap M b₁).alpha b₂N) ≠
      (EdgeDeletion.toCombMap M b₁).faceOf (l₁.head hl₁ne) := fun h' =>
    hface₂ (((hcyc₁.mem_iff _).mp hmemb₂).trans h'.symm)
  have hOg₂ : (EdgeDeletion.toCombMap M b₁).faceOf ((EdgeDeletion.toCombMap M b₁).alpha b₂N) ≠
      (EdgeDeletion.toCombMap M b₁).faceOf (V₁.outer.head V₁.outer_cycle.ne_nil) := by
    intro h
    have hMf := C₁.faceOf_value_eq hne₁ hl₁ hx₀₁ h hoffα
    exact hΣO ((congrArg M.faceOf hvα).symm.trans (hMf.trans (congrArg M.faceOf hheadO₁)))
  have hN₁planar := EdgeDeletion.planar_of_neFace M b₁ hM (l₁.head hl₁ne) C₁.face_ne
  by_cases hne₂ : C₂.xs ++ C₂.ys = []
  · -- the merged face would be empty: the remaining edge carries the outer face
    exfalso
    have hxs₂ : C₂.xs = [] := (List.append_eq_nil_iff.mp hne₂).1
    have hys₂ : C₂.ys = [] := (List.append_eq_nil_iff.mp hne₂).2
    have hfa : (EdgeDeletion.toCombMap M b₁).facePerm b₂N = b₂N := by
      have h := C₂.facePerm_getD_last_xs
      rw [hxs₂] at h
      exact h
    have hfαa : (EdgeDeletion.toCombMap M b₁).facePerm
        ((EdgeDeletion.toCombMap M b₁).alpha b₂N) = (EdgeDeletion.toCombMap M b₁).alpha b₂N := by
      have h := C₂.facePerm_getD_last_ys
      rw [hys₂] at h
      exact h
    have hσa : (EdgeDeletion.toCombMap M b₁).sigma b₂N =
        (EdgeDeletion.toCombMap M b₁).alpha b₂N := by
      rw [(EdgeDeletion.toCombMap M b₁).sigma_eq_facePerm_alpha, hfαa]
    have hσαa : (EdgeDeletion.toCombMap M b₁).sigma
        ((EdgeDeletion.toCombMap M b₁).alpha b₂N) = b₂N := by
      rw [(EdgeDeletion.toCombMap M b₁).sigma_eq_facePerm_alpha,
        (EdgeDeletion.toCombMap M b₁).alpha_involutive, hfa]
    rcases (EdgeDeletion.toCombMap M b₁).dart_eq_or_alpha_of_swapped_endpoints hN₁planar.1
        b₂N hσa hσαa (V₁.outer.head V₁.outer_cycle.ne_nil) with h | h
    · exact hOa₂ (congrArg (EdgeDeletion.toCombMap M b₁).faceOf h.symm)
    · exact hOg₂ (congrArg (EdgeDeletion.toCombMap M b₁).faceOf h.symm)
  -- the second merge: the merged face and `Σ`
  obtain ⟨l₂, hl₂⟩ := EdgeDeletion.exists_map_value_eq (EdgeDeletion.toCombMap M b₁) b₂N
    (C₂.xs ++ C₂.ys) fun d hd => C₂.avoid hd
  have hl₂ne : l₂ ≠ [] := by
    rintro rfl
    exact hne₂ hl₂.symm
  have hmap₂ : (C₂.xs ++ C₂.ys).map (EdgeDeletion.value M b₁) = zs ++ xs ++ us ++ ws := by
    have e1 : C₂.xs.map (EdgeDeletion.value M b₁) = zs ++ xs ++ us := by
      rw [hC₂x]
      exact htail₁
    have e2 : C₂.ys.map (EdgeDeletion.value M b₁) = ws := by
      rw [hC₂y]
      exact htailΣ
    exact List.map_append.trans (congrArg₂ (· ++ ·) e1 e2)
  have htrivF₂ : RelLetter.listVal
      ((C₂.xs ++ C₂.ys).map fun e => label (EdgeDeletion.value M b₁ e)) = 1 := by
    have e : ((C₂.xs ++ C₂.ys).map fun e => label (EdgeDeletion.value M b₁ e)) =
        (zs ++ xs ++ us ++ ws).map label :=
      (List.map_map (g := label) (f := EdgeDeletion.value M b₁)
        (l := C₂.xs ++ C₂.ys)).symm.trans (congrArg (List.map label) hmap₂)
    rw [e]
    exact hval
  obtain ⟨V₂, hV₂outer, _, hV₂card⟩ := V₁.exists_merge C₂ hne₂ hl₂ hl₂ne hOa₂ hOg₂ False
    (fun h => h.elim) (fun _ => htrivF₂)
  have hb₂rel : (EdgeDeletion.toCombMap M b₁).faceOf b₂N ∈ V₁.relFaces :=
    (hV₁mem _).mpr (Or.inr ⟨(hcyc₁.mem_iff _).mp hmemb₂, trivial⟩)
  have hαb₂rel : (EdgeDeletion.toCombMap M b₁).faceOf ((EdgeDeletion.toCombMap M b₁).alpha b₂N) ∈
      V₁.relFaces := by
    refine (hV₁mem _).mpr (Or.inl ⟨hoffα, ?_⟩)
    have hq : (EdgeDeletion.toCombMap M b₁).faceOf
        (Quotient.out ((EdgeDeletion.toCombMap M b₁).faceOf
          ((EdgeDeletion.toCombMap M b₁).alpha b₂N))) =
          (EdgeDeletion.toCombMap M b₁).faceOf ((EdgeDeletion.toCombMap M b₁).alpha b₂N) :=
      Quotient.out_eq _
    have hMf := C₁.faceOf_value_eq hne₁ hl₁ hx₀₁ hq (fun h => hoffα (hq.symm.trans h))
    exact (congrArg (fun z => z ∈ V.relFaces) (hMf.trans (congrArg M.faceOf hvα))).mpr hΣrel
  have hcard₂ : V₂.relFaces.card + 2 = V₁.relFaces.card := by
    simp only [if_pos hb₂rel, if_pos hαb₂rel, if_neg not_false] at hV₂card
    omega
  have hN₂planar := EdgeDeletion.planar_of_neFace (EdgeDeletion.toCombMap M b₁) b₂N hN₁planar
    (l₂.head hl₂ne) C₂.face_ne
  have hlabel₁ : ∀ e, (fun e => label (EdgeDeletion.value M b₁ e))
      ((EdgeDeletion.toCombMap M b₁).alpha e) =
        RelWord.inv ((fun e => label (EdgeDeletion.value M b₁ e)) e) := by
    intro e
    show label (EdgeDeletion.value M b₁ (EdgeDeletion.alpha M b₁ e)) = _
    rw [EdgeDeletion.alpha_val, hlabel]
  have hprod := V₂.isRelatorProduct hN₂planar (fun e => by
    show label (EdgeDeletion.value M b₁ (EdgeDeletion.value (EdgeDeletion.toCombMap M b₁) b₂N
      (EdgeDeletion.alpha (EdgeDeletion.toCombMap M b₁) b₂N e))) = _
    rw [EdgeDeletion.alpha_val]
    exact hlabel₁ _)
  have hmapO : RelLetter.listVal (V₂.outer.map fun e =>
      (fun e => label (EdgeDeletion.value M b₁ e))
        (EdgeDeletion.value (EdgeDeletion.toCombMap M b₁) b₂N e)) =
        RelLetter.listVal (V.outer.map label) :=
    congrArg RelLetter.listVal ((List.map_map (g := fun e => label (EdgeDeletion.value M b₁ e))
      (f := EdgeDeletion.value (EdgeDeletion.toCombMap M b₁) b₂N) (l := V₂.outer)).symm.trans
      ((congrArg (List.map fun e => label (EdgeDeletion.value M b₁ e)) hV₂outer).trans
        ((List.map_map (g := label) (f := EdgeDeletion.value M b₁) (l := V₁.outer)).symm.trans
          (congrArg (List.map label) hV₁outer))))
  rw [show V.relFaces.card - 2 = V₂.relFaces.card by omega, ← hmapO]
  exact hprod

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.VanKampenData.isRelatorProduct_sub_two
