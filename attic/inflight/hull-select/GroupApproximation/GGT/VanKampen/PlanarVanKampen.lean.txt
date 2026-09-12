import GroupApproximation.GGT.VanKampen.EdgeDeletionFaceCycles
import GroupApproximation.GGT.VanKampen.OneFaceWordTrivial
import GroupApproximation.GGT.VanKampen.CombMapEdgeDeletionEuler
import GroupApproximation.GroupTheory.NormalClosureReducedProduct
import GroupApproximation.Meta.AxiomGuard

/-!
# The planar van Kampen lemma

Let a planar combinatorial map carry relative letters on its darts with
`label (alpha d) = inv (label d)`, and choose an outer face `O` and a set of relator
faces not containing `O`.  If every relator face reads a signed conjugate of a
relator and every other inner face reads a freely trivial word, then the outer face
reads a product of relator conjugates with exactly one factor for each relator
face: `planarVanKampen`, spelled `PlanarVanKampenStatement`.

The proof is the classical ear induction on the number of darts
(`isRelatorProduct_of_planar`, stated over face cycles).

* The tree case is `listVal_faceBoundary_eq_one_of_faceCount_eq_one`.
* Otherwise the outer face has an edge whose other side is a different face `g`
  (`CombMap.exists_dart_faceOf_alpha_ne`).  Writing the two faces from that edge as
  `a :: xs` and `alpha a :: ys` (`EdgeDeletion.MergeCycles`), deleting the edge keeps
  the map planar (`EdgeDeletion.planar_of_neFace`), merges `g` into the outer face
  as `xs ++ ys`, and keeps every other face.  Since
  `val (a :: xs) = val a * val (xs ++ ys) * val (alpha a :: ys)⁻¹ * (val a)⁻¹`, one
  relator factor is added exactly when `g` is a relator face.
* When `xs` and `ys` are both empty the map is a single edge
  (`isRelatorProduct_of_isolated_edge`).
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv HullSC RelatorDefectBudget

universe u w v

section Rotate

variable {G : Type u} [Group G] {Lambda : Type w}

/-- A relator product bound survives undoing a rotation of the word. -/
theorem isRelatorProduct_of_rotate {R : Set G} {m : ℕ} (l : List (RelLetter G Lambda))
    {k : ℕ} (hk : k ≤ l.length)
    (h : IsRelatorProduct R m (RelLetter.listVal (l.rotate k))) :
    IsRelatorProduct R m (RelLetter.listVal l) := by
  rw [RelWord.listVal_rotate l hk] at h
  simpa [mul_assoc] using h.conj (RelLetter.listVal (l.take k))

/-- A signed conjugate survives a rotation of the word. -/
theorem isSignedConjugate_rotate {R : Set G} (l : List (RelLetter G Lambda)) {k : ℕ}
    (hk : k ≤ l.length) (h : IsSignedConjugate R (RelLetter.listVal l)) :
    IsSignedConjugate R (RelLetter.listVal (l.rotate k)) := by
  rw [RelWord.listVal_rotate l hk]
  simpa using h.conj (RelLetter.listVal (l.take k))⁻¹

/-- A freely trivial word stays trivial under rotation. -/
theorem listVal_rotate_eq_one (l : List (RelLetter G Lambda)) {k : ℕ} (hk : k ≤ l.length)
    (h : RelLetter.listVal l = 1) : RelLetter.listVal (l.rotate k) = 1 := by
  rw [RelWord.listVal_rotate l hk, h]
  simp

/-- A signed conjugate of a relator is a relator product with one factor. -/
theorem isRelatorProduct_one_of_isSignedConjugate {R : Set G} {x : G}
    (h : IsSignedConjugate R x) : IsRelatorProduct R 1 x := by
  obtain ⟨c, r, hr, hx | hx⟩ := h
  · rw [hx]
    exact (IsRelatorProduct.base hr).conj c
  · rw [hx]
    exact (IsRelatorProduct.base hr).inv.conj c

end Rotate

/-- **The isolated edge.**  In a connected map made of one edge on two distinct
faces, the outer face reads a relator product with one factor for each relator
face. -/
theorem isRelatorProduct_of_isolated_edge {G : Type u} [Group G] {Lambda : Type w}
    {R : Set G} {M : CombMap.{v}} (hM : M.IsConnected) (label : M.Dart → RelLetter G Lambda)
    (hlabel : ∀ d, label (M.alpha d) = RelWord.inv (label d)) {a : M.Dart}
    (hfa : M.facePerm a = a) (hfαa : M.facePerm (M.alpha a) = M.alpha a)
    (relFaces : Finset M.Face) (hOrel : M.faceOf a ∉ relFaces)
    (hrel : M.faceOf (M.alpha a) ∈ relFaces →
      IsSignedConjugate R (RelLetter.listVal [label (M.alpha a)]))
    (htriv : M.faceOf (M.alpha a) ∉ relFaces →
      RelLetter.listVal [label (M.alpha a)] = 1) :
    IsRelatorProduct R relFaces.card (RelLetter.listVal [label a]) := by
  have hσa : M.sigma a = M.alpha a := by
    rw [M.sigma_eq_facePerm_alpha, hfαa]
  have hσαa : M.sigma (M.alpha a) = a := by
    rw [M.sigma_eq_facePerm_alpha, M.alpha_involutive, hfa]
  have hall := M.dart_eq_or_alpha_of_swapped_endpoints hM a hσa hσαa
  have hfaces : ∀ f : M.Face, f = M.faceOf a ∨ f = M.faceOf (M.alpha a) := by
    intro f
    obtain ⟨d, rfl⟩ := Quotient.exists_rep f
    rcases hall d with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hval : RelLetter.listVal [label (M.alpha a)] = (RelLetter.listVal [label a])⁻¹ := by
    simp only [RelWord.listVal_cons, GGT.RelLetter.listVal_nil, mul_one, hlabel,
      RelWord.val_inv]
  by_cases hg : M.faceOf (M.alpha a) ∈ relFaces
  · have hcard : relFaces = {M.faceOf (M.alpha a)} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hg, fun f hf => by
        rcases hfaces f with rfl | rfl
        · exact absurd hf hOrel
        · rfl⟩
    rw [hcard, Finset.card_singleton]
    have h1 := isRelatorProduct_one_of_isSignedConjugate (hrel hg)
    rw [hval] at h1
    simpa using h1.inv
  · have hcard : relFaces = ∅ := Finset.eq_empty_of_forall_notMem fun f hf => by
      rcases hfaces f with rfl | rfl
      · exact hOrel hf
      · exact hg hf
    rw [hcard, Finset.card_empty]
    have h1 := htriv hg
    rw [hval, inv_eq_one] at h1
    rw [h1]
    exact IsRelatorProduct.one

/-- **The planar van Kampen lemma, over face cycles.** -/
theorem isRelatorProduct_of_planar {G : Type u} [Group G] {Lambda : Type w} (R : Set G) :
    ∀ (n : ℕ) (M : CombMap.{v}), M.dartCount = n → M.IsPlanar →
    ∀ (label : M.Dart → RelLetter G Lambda),
      (∀ d, label (M.alpha d) = RelWord.inv (label d)) →
    ∀ (relFaces : Finset M.Face) (lO : List M.Dart) (hO : M.IsFaceCycle lO),
      M.faceOf (lO.head hO.ne_nil) ∉ relFaces →
      (∀ (l : List M.Dart) (hl : M.IsFaceCycle l), M.faceOf (l.head hl.ne_nil) ∈ relFaces →
        IsSignedConjugate R (RelLetter.listVal (l.map label))) →
      (∀ (l : List M.Dart) (hl : M.IsFaceCycle l),
        M.faceOf (l.head hl.ne_nil) ≠ M.faceOf (lO.head hO.ne_nil) →
        M.faceOf (l.head hl.ne_nil) ∉ relFaces → RelLetter.listVal (l.map label) = 1) →
      IsRelatorProduct R relFaces.card (RelLetter.listVal (lO.map label)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M hn hM label hlabel relFaces lO hO hOrel hrel htriv
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
    rw [hempty, Finset.card_empty, hval]
    exact IsRelatorProduct.one
  obtain ⟨a, haO, hag⟩ :=
    M.exists_dart_faceOf_alpha_ne hM.1 (M.faceOf (lO.head hO.ne_nil)) hF
  have hface : M.faceOf a ≠ M.faceOf (M.alpha a) := fun h => hag (h.symm.trans haO)
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
  have hrotval : ∀ {m : ℕ},
      IsRelatorProduct R m (RelLetter.listVal ((a :: C.xs).map label)) →
        IsRelatorProduct R m (RelLetter.listVal (lO.map label)) := by
    intro m h
    refine isRelatorProduct_of_rotate (lO.map label) (k := k)
      (by rw [List.length_map]; exact hk) ?_
    rw [← List.map_rotate, hrot]
    exact h
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
    apply hrotval
    rw [hxs]
    refine isRelatorProduct_of_isolated_edge hM.1 label hlabel hfa hfαa relFaces
      (haO ▸ hOrel) (fun h => ?_) (fun h => ?_)
    · have hsc := hrel _ hg h
      rw [hys] at hsc
      exact hsc
    · have hone := htriv _ hg hgO h
      rw [hys] at hone
      exact hone
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
  have hrel' : ∀ (l' : List (EdgeDeletion.Dart M a))
      (hl' : (EdgeDeletion.toCombMap M a).IsFaceCycle l'),
      (EdgeDeletion.toCombMap M a).faceOf (l'.head hl'.ne_nil) ∈ relFaces' →
      IsSignedConjugate R
        (RelLetter.listVal (l'.map fun e => label (EdgeDeletion.value M a e))) := by
    intro l' hl' h
    obtain ⟨hoff, hin⟩ := (hmem' _).mp h
    have hM' := C.isFaceCycle_map_value_of_ne hnil hl hx₀ hl' hoff
    have hface' : M.faceOf ((l'.map (EdgeDeletion.value M a)).head hM'.ne_nil) ∈ relFaces := by
      rw [List.head_map, ← hout _ hoff]
      exact hin
    have hsc := hrel _ hM' hface'
    rwa [List.map_map] at hsc
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
  have hIH := ih _ hNcount (EdgeDeletion.toCombMap M a) rfl hNplanar
    (fun e => label (EdgeDeletion.value M a e)) hlabelN relFaces' l hcyc
    (fun h => ((hmem' _).mp h).1 rfl) hrel' htriv'
  have hlist : (l.map fun e => label (EdgeDeletion.value M a e)) = (C.xs ++ C.ys).map label := by
    rw [← hl]
    exact List.map_map.symm
  have hIH' : IsRelatorProduct R relFaces'.card
      (RelLetter.listVal (C.xs.map label) * RelLetter.listVal (C.ys.map label)) := by
    have e : RelLetter.listVal (C.xs.map label) * RelLetter.listVal (C.ys.map label) =
        RelLetter.listVal (l.map fun e => label (EdgeDeletion.value M a e)) := by
      rw [hlist, List.map_append, RelWord.listVal_append]
    rw [e]
    exact hIH
  have hcardE : relFaces'.card = (relFaces.erase (M.faceOf (M.alpha a))).card := by
    refine Finset.card_nbij (fun f => M.faceOf (EdgeDeletion.value M a (Quotient.out f)))
      ?_ ?_ ?_
    · intro f hf
      obtain ⟨hoff, hin⟩ := (hmem' f).mp (Finset.mem_coe.mp hf)
      have hq : (EdgeDeletion.toCombMap M a).faceOf (Quotient.out f) = f := Quotient.out_eq f
      exact Finset.mem_coe.mpr (Finset.mem_erase.mpr
        ⟨(C.faceOf_value_ne hnil hl hx₀ (fun h => hoff (hq.symm.trans h))).2, hin⟩)
    · intro f₁ hf₁ f₂ _ heq
      obtain ⟨hoff₁, -⟩ := (hmem' f₁).mp (Finset.mem_coe.mp hf₁)
      have hq₁ : (EdgeDeletion.toCombMap M a).faceOf (Quotient.out f₁) = f₁ := Quotient.out_eq f₁
      have hq₂ : (EdgeDeletion.toCombMap M a).faceOf (Quotient.out f₂) = f₂ := Quotient.out_eq f₂
      exact hq₁.symm.trans ((C.faceOf_eq_of_faceOf_value_eq hnil hl hx₀
        (fun h => hoff₁ (hq₁.symm.trans h)) heq).trans hq₂)
    · intro f hf
      obtain ⟨hne_g, hin⟩ := Finset.mem_erase.mp (Finset.mem_coe.mp hf)
      obtain ⟨d, rfl⟩ := Quotient.exists_rep f
      have hdO : M.faceOf d ≠ M.faceOf a := fun h =>
        hOrel ((congrArg (fun z => z ∈ relFaces) (h.trans haO)).mp hin)
      obtain ⟨x, hxd, hxoff⟩ := C.exists_value_eq_of_faceOf_ne hnil hl hx₀ hdO hne_g
      refine ⟨(EdgeDeletion.toCombMap M a).faceOf x,
        Finset.mem_coe.mpr ((hmem' _).mpr ⟨hxoff, ?_⟩), ?_⟩
      · exact (congrArg (fun z => z ∈ relFaces)
          ((hout x hxoff).trans (congrArg M.faceOf hxd))).mpr hin
      · exact (hout x hxoff).trans (congrArg M.faceOf hxd)
  have hOval : RelLetter.listVal ((a :: C.xs).map label) =
      (label a).val * RelLetter.listVal (C.xs.map label) := by
    rw [List.map_cons, RelWord.listVal_cons]
  have hgval : RelLetter.listVal ((M.alpha a :: C.ys).map label) =
      (label a).val⁻¹ * RelLetter.listVal (C.ys.map label) := by
    rw [List.map_cons, RelWord.listVal_cons, hlabel, RelWord.val_inv]
  apply hrotval
  by_cases hgrel : M.faceOf (M.alpha a) ∈ relFaces
  · have hcard : relFaces.card = relFaces'.card + 1 := by
      rw [hcardE, Finset.card_erase_add_one hgrel]
    have hsc := isRelatorProduct_one_of_isSignedConjugate (hrel _ hg hgrel)
    rw [hgval] at hsc
    have hprod := (hIH'.mul hsc.inv).conj (label a).val
    have heq : (label a).val * RelLetter.listVal (C.xs.map label) =
        (label a).val * (RelLetter.listVal (C.xs.map label) *
          RelLetter.listVal (C.ys.map label) *
            ((label a).val⁻¹ * RelLetter.listVal (C.ys.map label))⁻¹) * (label a).val⁻¹ := by
      group
    rw [hcard, hOval, heq]
    exact hprod
  · have hcard : relFaces.card = relFaces'.card := by
      rw [hcardE, Finset.erase_eq_of_notMem hgrel]
    have hone := htriv _ hg hgO hgrel
    rw [hgval] at hone
    have hY : RelLetter.listVal (C.ys.map label) = (label a).val := by
      have h := congrArg ((label a).val * ·) hone
      simpa using h
    have hprod := hIH'.conj (label a).val
    have heq : (label a).val * RelLetter.listVal (C.xs.map label) =
        (label a).val * (RelLetter.listVal (C.xs.map label) *
          RelLetter.listVal (C.ys.map label)) * (label a).val⁻¹ := by
      rw [hY]
      group
    rw [hcard, hOval, heq]
    exact hprod

/-- **The planar van Kampen statement.**  In a planar map with an outer face `O` and
a set of relator faces not containing `O`, if every relator face reads a signed
conjugate of a relator and every other inner face reads a freely trivial word, the
outer face reads a relator product with one factor for each relator face. -/
def PlanarVanKampenStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (R : Set G) (M : CombMap.{v}), M.IsPlanar →
    ∀ (label : M.Dart → RelLetter G Lambda),
      (∀ d, label (M.alpha d) = RelWord.inv (label d)) →
    ∀ (O : M.Face) (FB : ∀ f, FaceBoundary M f) (relFaces : Finset M.Face), O ∉ relFaces →
      (∀ f ∈ relFaces, IsSignedConjugate R (RelLetter.listVal ((FB f).darts.map label))) →
      (∀ f, f ≠ O → f ∉ relFaces → RelLetter.listVal ((FB f).darts.map label) = 1) →
      IsRelatorProduct R relFaces.card (RelLetter.listVal ((FB O).darts.map label))

/-- **The planar van Kampen lemma.** -/
theorem planarVanKampen : PlanarVanKampenStatement.{u, w, v} := by
  intro G _ Lambda R M hM label hlabel O FB relFaces hOrel hrel htriv
  refine isRelatorProduct_of_planar R M.dartCount M rfl hM label hlabel relFaces (FB O).darts
    (FB O).isFaceCycle (by rw [FaceBoundary.faceOf_head]; exact hOrel) ?_ ?_
  · intro l hl hf
    obtain ⟨k, hk, hrot⟩ := (FB (M.faceOf (l.head hl.ne_nil))).isFaceCycle.exists_rotate_eq hl
      (FaceBoundary.faceOf_head _)
    rw [← hrot, List.map_rotate]
    exact isSignedConjugate_rotate _ (by rw [List.length_map]; exact hk) (hrel _ hf)
  · intro l hl hne hf
    obtain ⟨k, hk, hrot⟩ := (FB (M.faceOf (l.head hl.ne_nil))).isFaceCycle.exists_rotate_eq hl
      (FaceBoundary.faceOf_head _)
    rw [← hrot, List.map_rotate]
    have hne' : M.faceOf (l.head hl.ne_nil) ≠ O := by
      rwa [FaceBoundary.faceOf_head] at hne
    exact listVal_rotate_eq_one _ (by rw [List.length_map]; exact hk) (htriv _ hne' hf)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.isRelatorProduct_of_isolated_edge
#audit_axioms GroupApproximation.GGT.VanKampen.isRelatorProduct_of_planar
#audit_axioms GroupApproximation.GGT.VanKampen.planarVanKampen
