import GroupApproximation.GGT.VanKampen.PlanarVanKampenCellSteps
import GroupApproximation.Meta.AxiomGuard

/-!
# The cellular planar van Kampen lemma

A planar map carries relative letters with `label (alpha d) = inv (label d)`, an outer
face cycle `lO`, and a set of relator faces not containing the outer face, every other
inner face reading a freely trivial word.  Then the outer word is an ordered product
with exactly one factor for each relator face, that factor being a signed conjugate of
the word read around the face: `exists_cellFactors_of_planar`.

This refines `isRelatorProduct_of_planar` (`PlanarVanKampen`) by recording which face
each factor comes from, which is what building a `DiscDiagram` with its ordered
relator cells and product formula needs.  The proof is the same ear induction.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv HullSC RelatorDefectBudget

universe u w v

/-- **The cellular planar van Kampen lemma, over face cycles.** -/
theorem exists_cellFactors_of_planar {G : Type u} [Group G] {Lambda : Type w} :
    ∀ (n : ℕ) (M : CombMap.{v}), M.dartCount = n → M.IsPlanar →
    ∀ (label : M.Dart → RelLetter G Lambda),
      (∀ d, label (M.alpha d) = RelWord.inv (label d)) →
    ∀ (relFaces : Finset M.Face) (lO : List M.Dart) (hO : M.IsFaceCycle lO),
      M.faceOf (lO.head hO.ne_nil) ∉ relFaces →
      (∀ (l : List M.Dart) (hl : M.IsFaceCycle l),
        M.faceOf (l.head hl.ne_nil) ≠ M.faceOf (lO.head hO.ne_nil) →
        M.faceOf (l.head hl.ne_nil) ∉ relFaces → RelLetter.listVal (l.map label) = 1) →
      ∃ factors : List (M.Face × G), (factors.map Prod.fst).Nodup ∧
        (∀ f, f ∈ factors.map Prod.fst ↔ f ∈ relFaces) ∧
        (∀ y ∈ factors, CellFactor M label y.1 y.2) ∧
        (factors.map Prod.snd).prod = RelLetter.listVal (lO.map label) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M hn hM label hlabel relFaces lO hO hOrel htriv
  classical
  have hFpos : 0 < M.faceCount := by
    haveI : Nonempty M.Face := ⟨M.faceOf (lO.head hO.ne_nil)⟩
    exact Nat.card_pos
  rcases Nat.lt_or_ge 1 M.faceCount with hF | hF
  swap
  · have hF1 : M.faceCount = 1 := by omega
    haveI : Subsingleton M.Face := (Nat.card_eq_one_iff_unique.mp hF1).1
    have hempty : relFaces = ∅ := Finset.eq_empty_of_forall_notMem fun f hf =>
      hOrel (by rwa [Subsingleton.elim f (M.faceOf (lO.head hO.ne_nil))] at hf)
    have hval : RelLetter.listVal (lO.map label) = 1 :=
      listVal_faceBoundary_eq_one_of_faceCount_eq_one M.edgeCount M rfl hM hF1 label hlabel
        _ hO.toFaceBoundary
    refine ⟨[], List.nodup_nil, fun f => by simp [hempty],
      fun y hy => absurd hy List.not_mem_nil, ?_⟩
    simp only [List.map_nil, List.prod_nil]
    exact hval.symm
  obtain ⟨a, haO, hag⟩ :=
    M.exists_dart_faceOf_alpha_ne hM.1 (M.faceOf (lO.head hO.ne_nil)) hF
  have hface : M.faceOf a ≠ M.faceOf (M.alpha a) := fun h => hag (h.symm.trans haO)
  have hOrel' : M.faceOf a ∉ relFaces := fun h =>
    hOrel ((congrArg (fun z => z ∈ relFaces) haO).mp h)
  obtain ⟨k, xs, hk, hrot⟩ := hO.exists_rotate_cons ((hO.mem_iff a).mpr haO)
  have hOrot : M.IsFaceCycle (a :: xs) := hrot ▸ hO.rotate k
  obtain ⟨lg, hg, hghead⟩ := M.exists_isFaceCycle_head (M.alpha a)
  obtain ⟨ys, rfl⟩ : ∃ ys, lg = M.alpha a :: ys := by
    cases lg with
    | nil => exact absurd rfl hg.ne_nil
    | cons y ys => exact ⟨ys, by rw [show y = M.alpha a from hghead]⟩
  obtain ⟨C, hCx, hCy⟩ : ∃ C : EdgeDeletion.MergeCycles M a, C.xs = xs ∧ C.ys = ys :=
    ⟨⟨xs, ys, hOrot, hg, hface⟩, rfl, rfl⟩
  subst hCx hCy
  have hgO : M.faceOf ((M.alpha a :: C.ys).head hg.ne_nil) ≠ M.faceOf (lO.head hO.ne_nil) :=
    hag
  have hrotfac : ∀ factors : List (M.Face × G), (factors.map Prod.fst).Nodup →
      (∀ f, f ∈ factors.map Prod.fst ↔ f ∈ relFaces) →
      (∀ y ∈ factors, CellFactor M label y.1 y.2) →
      (factors.map Prod.snd).prod = RelLetter.listVal ((a :: C.xs).map label) →
      ∃ factors : List (M.Face × G), (factors.map Prod.fst).Nodup ∧
        (∀ f, f ∈ factors.map Prod.fst ↔ f ∈ relFaces) ∧
        (∀ y ∈ factors, CellFactor M label y.1 y.2) ∧
        (factors.map Prod.snd).prod = RelLetter.listVal (lO.map label) := by
    intro factors hnd hiff hfac hprod
    obtain ⟨factors', hfst, hfac', hprod'⟩ := exists_cellFactors_of_rotate lO hk factors hfac
      (by rw [hrot]; exact hprod)
    exact ⟨factors', (congrArg List.Nodup hfst).mpr hnd,
      fun f => (congrArg (fun L => f ∈ L ↔ f ∈ relFaces) hfst).mpr (hiff f), hfac', hprod'⟩
  by_cases hnil : C.xs ++ C.ys = []
  · have hxs : C.xs = [] := (List.append_eq_nil_iff.mp hnil).1
    have hys : C.ys = [] := (List.append_eq_nil_iff.mp hnil).2
    have hfa : M.facePerm a = a := by
      have h := C.facePerm_getD_last_xs
      rw [hxs] at h
      exact h
    have hfαa : M.facePerm (M.alpha a) = M.alpha a := by
      have h := C.facePerm_getD_last_ys
      rw [hys] at h
      exact h
    have hcycα : M.IsFaceCycle [M.alpha a] := by
      have h := hg
      rw [hys] at h
      exact h
    obtain ⟨factors, hnd, hiff, hfac, hprod⟩ := exists_cellFactors_of_isolated_edge hM.1 label
      hlabel hfa hfαa hcycα relFaces hOrel' (fun h => by
        have hone := htriv _ hg hgO h
        rw [hys] at hone
        exact hone)
    refine hrotfac factors hnd hiff hfac ?_
    rw [hxs]
    exact hprod
  obtain ⟨l, hl⟩ := EdgeDeletion.exists_map_value_eq M a (C.xs ++ C.ys) fun d hd => C.avoid hd
  have hlne : l ≠ [] := by
    rintro rfl
    exact hnil hl.symm
  have hcyc := C.isFaceCycle_lift hnil hl
  have hx₀ : l.head hlne ∈ l := List.head_mem hlne
  have hNplanar := EdgeDeletion.planar_of_neFace M a hM (l.head hlne) hface
  have hNcount : (EdgeDeletion.toCombMap M a).dartCount < n := by
    have := EdgeDeletion.dartCount_add_two M a
    omega
  have hlabelN : ∀ e, (fun e => label (EdgeDeletion.value M a e))
      ((EdgeDeletion.toCombMap M a).alpha e) =
        RelWord.inv ((fun e => label (EdgeDeletion.value M a e)) e) := by
    intro e
    show label (EdgeDeletion.value M a (EdgeDeletion.alpha M a e)) = _
    rw [EdgeDeletion.alpha_val, hlabel]
  obtain ⟨relFaces', hmem'⟩ : ∃ s : Finset (EdgeDeletion.toCombMap M a).Face, ∀ f,
      f ∈ s ↔ (f ≠ (EdgeDeletion.toCombMap M a).faceOf (l.head hlne) ∧
        M.faceOf (EdgeDeletion.value M a (Quotient.out f)) ∈ relFaces) :=
    ⟨Finset.univ.filter fun f => f ≠ (EdgeDeletion.toCombMap M a).faceOf (l.head hlne) ∧
        M.faceOf (EdgeDeletion.value M a (Quotient.out f)) ∈ relFaces, fun f => by simp⟩
  have hout : ∀ x : EdgeDeletion.Dart M a,
      (EdgeDeletion.toCombMap M a).faceOf x ≠ (EdgeDeletion.toCombMap M a).faceOf (l.head hlne) →
      M.faceOf (EdgeDeletion.value M a (Quotient.out ((EdgeDeletion.toCombMap M a).faceOf x))) =
        M.faceOf (EdgeDeletion.value M a x) := by
    intro x hx
    have hq : (EdgeDeletion.toCombMap M a).faceOf
        (Quotient.out ((EdgeDeletion.toCombMap M a).faceOf x)) =
          (EdgeDeletion.toCombMap M a).faceOf x :=
      Quotient.out_eq _
    exact C.faceOf_value_eq hnil hl hx₀ hq (fun h => hx (hq.symm.trans h))
  have htriv' : ∀ (l' : List (EdgeDeletion.Dart M a))
      (hl' : (EdgeDeletion.toCombMap M a).IsFaceCycle l'),
      (EdgeDeletion.toCombMap M a).faceOf (l'.head hl'.ne_nil) ≠
        (EdgeDeletion.toCombMap M a).faceOf (l.head hcyc.ne_nil) →
      (EdgeDeletion.toCombMap M a).faceOf (l'.head hl'.ne_nil) ∉ relFaces' →
      RelLetter.listVal (l'.map fun e => label (EdgeDeletion.value M a e)) = 1 := by
    intro l' hl' hoff hnotin
    have hoff' : (EdgeDeletion.toCombMap M a).faceOf (l'.head hl'.ne_nil) ≠
        (EdgeDeletion.toCombMap M a).faceOf (l.head hlne) := hoff
    have hM' := C.isFaceCycle_map_value_of_ne hnil hl hx₀ hl' hoff'
    have hnot : M.faceOf ((l'.map (EdgeDeletion.value M a)).head hM'.ne_nil) ∉ relFaces := by
      rw [List.head_map, ← hout _ hoff']
      exact fun h => hnotin ((hmem' _).mpr ⟨hoff', h⟩)
    have hneO : M.faceOf ((l'.map (EdgeDeletion.value M a)).head hM'.ne_nil) ≠
        M.faceOf (lO.head hO.ne_nil) := by
      rw [List.head_map, ← haO]
      exact (C.faceOf_value_ne hnil hl hx₀ hoff').1
    have hone := htriv _ hM' hneO hnot
    rwa [List.map_map] at hone
  obtain ⟨factorsN, hndN, hiffN, hfacN, hprodN⟩ := ih _ hNcount (EdgeDeletion.toCombMap M a)
    rfl hNplanar (fun e => label (EdgeDeletion.value M a e)) hlabelN relFaces' l hcyc
    (fun h => ((hmem' _).mp h).1 rfl) htriv'
  -- the faces of the deleted map, read in the original map
  have hφinj : ∀ F₁ ∈ relFaces', ∀ F₂ ∈ relFaces',
      M.faceOf (EdgeDeletion.value M a (Quotient.out F₁)) =
        M.faceOf (EdgeDeletion.value M a (Quotient.out F₂)) → F₁ = F₂ := by
    intro F₁ hF₁ F₂ _ heq
    obtain ⟨hoff₁, -⟩ := (hmem' F₁).mp hF₁
    have hq₁ : (EdgeDeletion.toCombMap M a).faceOf (Quotient.out F₁) = F₁ := Quotient.out_eq F₁
    have hq₂ : (EdgeDeletion.toCombMap M a).faceOf (Quotient.out F₂) = F₂ := Quotient.out_eq F₂
    exact hq₁.symm.trans ((C.faceOf_eq_of_faceOf_value_eq hnil hl hx₀
      (fun h => hoff₁ (hq₁.symm.trans h)) heq).trans hq₂)
  have hφg : ∀ F ∈ relFaces',
      M.faceOf (EdgeDeletion.value M a (Quotient.out F)) ≠ M.faceOf (M.alpha a) := by
    intro F hF
    obtain ⟨hoff, -⟩ := (hmem' F).mp hF
    have hq : (EdgeDeletion.toCombMap M a).faceOf (Quotient.out F) = F := Quotient.out_eq F
    exact (C.faceOf_value_ne hnil hl hx₀ (x := Quotient.out F)
      (fun h => hoff (hq.symm.trans h))).2
  have hφsurj : ∀ f ∈ relFaces, f ≠ M.faceOf (M.alpha a) →
      ∃ F ∈ relFaces', M.faceOf (EdgeDeletion.value M a (Quotient.out F)) = f := by
    intro f hf hne_g
    obtain ⟨d, rfl⟩ := Quotient.exists_rep f
    have hdO : M.faceOf d ≠ M.faceOf a := fun h => hOrel' ((congrArg (fun z => z ∈ relFaces) h).mp hf)
    obtain ⟨x, hxd, hxoff⟩ := C.exists_value_eq_of_faceOf_ne hnil hl hx₀ hdO hne_g
    refine ⟨(EdgeDeletion.toCombMap M a).faceOf x, (hmem' _).mpr ⟨hxoff, ?_⟩, ?_⟩
    · exact (congrArg (fun z => z ∈ relFaces)
        ((hout x hxoff).trans (congrArg M.faceOf hxd))).mpr hf
    · exact (hout x hxoff).trans (congrArg M.faceOf hxd)
  have htrans : ∀ y ∈ factorsN,
      CellFactor M label (M.faceOf (EdgeDeletion.value M a (Quotient.out y.1))) y.2 := by
    intro y hy
    have hin : y.1 ∈ relFaces' := (hiffN _).mp (List.mem_map.mpr ⟨y, hy, rfl⟩)
    obtain ⟨hoffF, -⟩ := (hmem' _).mp hin
    obtain ⟨l', hl', c, hf', hx⟩ := hfacN y hy
    have hoff : (EdgeDeletion.toCombMap M a).faceOf (l'.head hl'.ne_nil) ≠
        (EdgeDeletion.toCombMap M a).faceOf (l.head hlne) := fun h => hoffF (hf'.symm.trans h)
    have hM' := C.isFaceCycle_map_value_of_ne hnil hl hx₀ hl' hoff
    have hword : RelLetter.listVal ((l'.map (EdgeDeletion.value M a)).map label) =
        RelLetter.listVal (l'.map fun e => label (EdgeDeletion.value M a e)) :=
      congrArg RelLetter.listVal
        (List.map_map (g := label) (f := EdgeDeletion.value M a) (l := l'))
    refine ⟨l'.map (EdgeDeletion.value M a), hM', c, ?_, ?_⟩
    · exact (congrArg M.faceOf (List.head_map hM'.ne_nil)).trans ((hout _ hoff).symm.trans
        (congrArg (fun F => M.faceOf (EdgeDeletion.value M a (Quotient.out F))) hf'))
    · exact (congrArg (fun z => y.2 = c * z * c⁻¹ ∨ y.2 = c * z⁻¹ * c⁻¹) hword).mpr hx
  -- values
  have hlist : (l.map fun e => label (EdgeDeletion.value M a e)) = (C.xs ++ C.ys).map label := by
    rw [← hl]
    exact List.map_map.symm
  have hprodN' : (factorsN.map Prod.snd).prod =
      RelLetter.listVal (C.xs.map label) * RelLetter.listVal (C.ys.map label) := by
    have e : RelLetter.listVal (C.xs.map label) * RelLetter.listVal (C.ys.map label) =
        RelLetter.listVal (l.map fun e => label (EdgeDeletion.value M a e)) := by
      rw [hlist, List.map_append, RelWord.listVal_append]
    rw [e]
    exact hprodN
  have hOval : RelLetter.listVal ((a :: C.xs).map label) =
      (label a).val * RelLetter.listVal (C.xs.map label) := by
    rw [List.map_cons, RelWord.listVal_cons]
  have hgval : RelLetter.listVal ((M.alpha a :: C.ys).map label) =
      (label a).val⁻¹ * RelLetter.listVal (C.ys.map label) := by
    rw [List.map_cons, RelWord.listVal_cons, hlabel, RelWord.val_inv]
  -- the transported factors
  obtain ⟨factors₁, hfactors₁⟩ : ∃ L : List (M.Face × G), L = factorsN.map fun y =>
      (M.faceOf (EdgeDeletion.value M a (Quotient.out y.1)),
        (label a).val * y.2 * ((label a).val)⁻¹) := ⟨_, rfl⟩
  have hmapfst := map_fst_map_conj (fun F : (EdgeDeletion.toCombMap M a).Face =>
    M.faceOf (EdgeDeletion.value M a (Quotient.out F))) (label a).val factorsN
  have hmapsnd := prod_map_snd_map_conj (fun F : (EdgeDeletion.toCombMap M a).Face =>
    M.faceOf (EdgeDeletion.value M a (Quotient.out F))) (label a).val factorsN
  have hnd₁ : (factors₁.map Prod.fst).Nodup := by
    rw [hfactors₁, hmapfst]
    exact List.Nodup.map_on (fun F hF F' hF' heq =>
      hφinj F ((hiffN F).mp hF) F' ((hiffN F').mp hF') heq) hndN
  have hiff₁ : ∀ f, f ∈ factors₁.map Prod.fst ↔ (f ∈ relFaces ∧ f ≠ M.faceOf (M.alpha a)) := by
    intro f
    rw [hfactors₁, hmapfst]
    constructor
    · intro hf
      obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hf
      have hF' := (hiffN F).mp hF
      exact ⟨((hmem' F).mp hF').2, hφg F hF'⟩
    · rintro ⟨hf, hne_g⟩
      obtain ⟨F, hF, hFf⟩ := hφsurj f hf hne_g
      exact List.mem_map.mpr ⟨F, (hiffN F).mpr hF, hFf⟩
  have hfac₁ : ∀ y ∈ factors₁, CellFactor M label y.1 y.2 := by
    rw [hfactors₁]
    intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    exact (htrans z hz).conj _
  have hprod₁ : (factors₁.map Prod.snd).prod = (label a).val *
      (RelLetter.listVal (C.xs.map label) * RelLetter.listVal (C.ys.map label)) *
        ((label a).val)⁻¹ := by
    rw [hfactors₁, hmapsnd, hprodN']
  by_cases hgrel : M.faceOf (M.alpha a) ∈ relFaces
  · refine hrotfac (factors₁ ++ [(M.faceOf (M.alpha a),
      (label a).val * ((label a).val⁻¹ * RelLetter.listVal (C.ys.map label))⁻¹ *
        ((label a).val)⁻¹)]) ?_ ?_ ?_ ?_
    · rw [List.map_append, List.nodup_append]
      refine ⟨hnd₁, List.nodup_singleton _, ?_⟩
      intro f hf f' hf' hff'
      rw [List.map_cons, List.map_nil, List.mem_singleton] at hf'
      exact ((hiff₁ f).mp hf).2 (hff'.trans hf')
    · intro f
      rw [List.map_append, List.mem_append, hiff₁, List.map_cons, List.map_nil,
        List.mem_singleton]
      constructor
      · rintro (⟨h, -⟩ | h)
        · exact h
        · exact (congrArg (fun z => z ∈ relFaces) h).mpr hgrel
      · intro hf
        by_cases hfg : f = M.faceOf (M.alpha a)
        · exact Or.inr hfg
        · exact Or.inl ⟨hf, hfg⟩
    · intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hfac₁ y hy
      · rw [List.mem_singleton] at hy
        subst hy
        refine ⟨M.alpha a :: C.ys, hg, (label a).val, rfl, Or.inr ?_⟩
        rw [hgval]
    · rw [List.map_append, List.prod_append, hprod₁, hOval]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      group
  · have hone := htriv _ hg hgO hgrel
    rw [hgval] at hone
    have hY : RelLetter.listVal (C.ys.map label) = (label a).val := by
      have h := congrArg ((label a).val * ·) hone
      simpa using h
    refine hrotfac factors₁ hnd₁ (fun f => ?_) hfac₁ ?_
    · rw [hiff₁]
      exact ⟨fun h => h.1, fun hf => ⟨hf, fun h =>
        hgrel ((congrArg (fun z => z ∈ relFaces) h).mp hf)⟩⟩
    · rw [hprod₁, hOval, hY]
      group

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.exists_cellFactors_of_planar
