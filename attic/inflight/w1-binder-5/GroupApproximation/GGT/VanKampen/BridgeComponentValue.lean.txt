import GroupApproximation.GGT.VanKampen.BridgeComponentPlanar
import GroupApproximation.GGT.VanKampen.PlanarVanKampen
import GroupApproximation.GGT.VanKampen.FaceCycle
import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import GroupApproximation.Meta.AxiomGuard

/-!
# Deleting a same-face bridge: a cell-free pocket reads one

Osin (math/0411039v3, §9), proof of Lemma 9.4.  Let `a` be an oriented dart of a disc diagram whose
reverse lies on the same face, and let `f a, …, fᵐ a` be the face walk strictly between `a` and
`α a`.  The walk is a face cycle of the far component of the deleted edge
(`BridgeComponent.component`), which is planar.  When no relator cell other than the face of `a`
has a dart on the far side, every other face of the component is a `G`-face, so the planar van
Kampen lemma (`isRelatorProduct_of_planar`) gives value one.
* `isFaceCycle_val`, `isFaceCycle_of_val`: face cycles of a restricted map.
* `listVal_pocket_eq_one`: the cell-free pocket value.

## Manuscript status

Infrastructure for `thm:hull` ("Hull's small cancellation theorem", through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

namespace BridgeComponent

section FaceCycles

variable {N : CombMap.{u}} (S : N.Dart → Prop) (hα : ∀ x, S (N.alpha x) ↔ S x)
  (hσ : ∀ x, S (N.sigma x) ↔ S x)

/-- **A face cycle of a restricted map is a face cycle of the map.** -/
theorem isFaceCycle_val {l : List (N.restrict S hα hσ).Dart}
    (hl : (N.restrict S hα hσ).IsFaceCycle l) : N.IsFaceCycle (l.map Subtype.val) := by
  refine ⟨fun h => hl.ne_nil (List.map_eq_nil_iff.mp h), hl.nodup.map Subtype.val_injective,
    ?_, ?_⟩
  · rw [List.isChain_map]
    exact hl.chain.imp fun x y h => by rw [← h]; rfl
  · rw [List.getLast_map, List.head_map]
    exact congrArg Subtype.val hl.closes

/-- **A list of the restricted map whose values form a face cycle is a face cycle.** -/
theorem isFaceCycle_of_val {l : List (N.restrict S hα hσ).Dart}
    (hl : N.IsFaceCycle (l.map Subtype.val)) : (N.restrict S hα hσ).IsFaceCycle l := by
  refine ⟨fun h => hl.ne_nil (List.map_eq_nil_iff.mpr h), hl.nodup.of_map _, ?_, ?_⟩
  · have h := hl.chain
    rw [List.isChain_map] at h
    exact h.imp fun x y hxy => Subtype.ext hxy
  · apply Subtype.ext
    have h := hl.closes
    rw [List.getLast_map, List.head_map] at h
    exact h

end FaceCycles

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A cell-free pocket reads one.**  Let `a` be a dart of a disc diagram, off the exterior,
oriented toward the exterior, with its reverse on its own face at `m + 1` face steps (`m > 0`).
If no relator cell other than the face of `a` has a dart joined to `α a` by moves avoiding the
edge, the face walk `f a, …, fᵐ a` reads one. -/
theorem listVal_pocket_eq_one (X : DiscDiagram.{u, w, v} W) [DecidableEq X.toCombMap.Dart]
    {a : X.toCombMap.Dart}
    (hface : X.toCombMap.faceOf a = X.toCombMap.faceOf (X.toCombMap.alpha a))
    (hout : X.toCombMap.faceOf a ≠ X.outerFace)
    (hor : AvoidEdgeStep.Oriented X.toCombMap X.outerFace a)
    {m : ℕ} (hm : 0 < m) (hstep : (X.toCombMap.facePerm ^ (m + 1)) a = X.toCombMap.alpha a)
    (hne_a : ∀ t, t < m + 1 → (X.toCombMap.facePerm ^ (t + 1)) a ≠ a)
    (hne_alpha : ∀ t, t < m → (X.toCombMap.facePerm ^ (t + 1)) a ≠ X.toCombMap.alpha a)
    (hfree : ∀ C ∈ X.relatorCells, C.face ≠ X.toCombMap.faceOf a →
      ∀ x, X.toCombMap.faceOf x = C.face →
        ¬ Relation.EqvGen (AvoidEdgeStep X.toCombMap a) x (X.toCombMap.alpha a)) :
    RelLetter.listVal (dartWord X
      ((List.range m).map fun t => (X.toCombMap.facePerm ^ (t + 1)) a)) = 1 := by
  have htail : X.toCombMap.sigma a ≠ a := by
    intro hfix
    obtain ⟨o, ho, hao⟩ := hor
    have hoa : o = a := (AvoidEdgeStep.eq_iff_of_sigma_fixed (Or.inl rfl) hfix hao).mp rfl
    exact hout (by rw [← ho, hoa])
  have hstart : X.toCombMap.sigma (X.toCombMap.alpha a) ≠ X.toCombMap.alpha a := by
    have h := hne_alpha 0 hm
    rwa [zero_add, pow_one] at h
  have hret : ∀ t, t < m → (X.toCombMap.facePerm ^ (t + 1)) a ≠ a ∧
      (X.toCombMap.facePerm ^ (t + 1)) a ≠ X.toCombMap.alpha a :=
    fun t ht => ⟨hne_a t (by omega), hne_alpha t ht⟩
  have hfstep : ∀ x : EdgeDeletion.Dart X.toCombMap a,
      Relation.EqvGen (EdgeDeletion.toCombMap X.toCombMap a).Adjacent x
        ((EdgeDeletion.toCombMap X.toCombMap a).facePerm x) := fun x =>
    Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ (Or.inl rfl))
      (Relation.EqvGen.rel _ _ (Or.inr rfl))
  have hnext : ∀ t, t + 1 < m →
      EdgeDeletion.next X.toCombMap a ((X.toCombMap.facePerm ^ (t + 1)) a) =
        (X.toCombMap.facePerm ^ (t + 1 + 1)) a := by
    intro t ht
    have e : X.toCombMap.facePerm ((X.toCombMap.facePerm ^ (t + 1)) a) =
        (X.toCombMap.facePerm ^ (t + 1 + 1)) a := by
      rw [pow_succ' _ (t + 1), Equiv.Perm.mul_apply]
    have h1 : X.toCombMap.facePerm ((X.toCombMap.facePerm ^ (t + 1)) a) ≠ a := by
      rw [e]
      exact hne_a (t + 1) (by omega)
    have h2 : X.toCombMap.facePerm ((X.toCombMap.facePerm ^ (t + 1)) a) ≠ X.toCombMap.alpha a := by
      rw [e]
      exact hne_alpha (t + 1) ht
    rw [EdgeDeletion.next_of_ne_of_ne _ _ h1 h2, e]
  have hlast : EdgeDeletion.next X.toCombMap a ((X.toCombMap.facePerm ^ m) a) =
      (X.toCombMap.facePerm ^ (0 + 1)) a := by
    have e : X.toCombMap.facePerm ((X.toCombMap.facePerm ^ m) a) = X.toCombMap.alpha a := by
      rw [← hstep, pow_succ', Equiv.Perm.mul_apply]
    have h1 : (X.toCombMap.facePerm ^ (0 + 1)) a = X.toCombMap.facePerm a := by
      rw [zero_add, pow_one]
    have hn1 : ¬ X.toCombMap.facePerm ((X.toCombMap.facePerm ^ m) a) = a := by
      rw [e]
      exact X.toCombMap.alpha_fixedPointFree a
    have hn2 : ¬ X.toCombMap.facePerm a = a := by
      rw [← h1]
      exact hne_a 0 (by omega)
    rw [EdgeDeletion.next, if_neg hn1, if_pos e, if_neg hn2, h1]
  have hside : ∀ t (ht : t < m), Side X.toCombMap a hface hstart
      (EdgeDeletion.ofValue X.toCombMap a ((X.toCombMap.facePerm ^ (t + 1)) a)
        (hret t ht).1 (hret t ht).2) := by
    intro t
    induction t with
    | zero =>
      intro ht
      have hd : near0 X.toCombMap a hface hstart = EdgeDeletion.ofValue X.toCombMap a
          ((X.toCombMap.facePerm ^ (0 + 1)) a) (hret 0 ht).1 (hret 0 ht).2 :=
        EdgeDeletion.value_injective _ _ (show X.toCombMap.sigma (X.toCombMap.alpha a) =
          (X.toCombMap.facePerm ^ (0 + 1)) a by rw [zero_add, pow_one]; rfl)
      rw [← hd]
      exact Relation.EqvGen.refl _
    | succ t ih =>
      intro ht
      have hN : (EdgeDeletion.toCombMap X.toCombMap a).facePerm
          (EdgeDeletion.ofValue X.toCombMap a ((X.toCombMap.facePerm ^ (t + 1)) a)
            (hret t (by omega)).1 (hret t (by omega)).2) =
          EdgeDeletion.ofValue X.toCombMap a ((X.toCombMap.facePerm ^ (t + 1 + 1)) a)
            (hret (t + 1) ht).1 (hret (t + 1) ht).2 :=
        (EdgeDeletion.facePerm_eq_iff _ _ _ _).mpr (hnext t ht)
      rw [← hN]
      exact Relation.EqvGen.trans _ _ _ (ih (by omega)) (hfstep _)
  -- The pocket walk as a face cycle of the far component.  The darts of the component are the
  -- darts of `{x // Side x}` only after unfolding, so the list lemmas below are applied in term
  -- mode, where unification sees through the restriction.
  obtain ⟨lO, hlO⟩ : ∃ lO : List (component X.toCombMap a hface hstart).Dart,
      lO = List.ofFn fun t : Fin m => ⟨EdgeDeletion.ofValue X.toCombMap a
        ((X.toCombMap.facePerm ^ (t.1 + 1)) a) (hret t.1 t.2).1 (hret t.1 t.2).2,
        hside t.1 t.2⟩ := ⟨_, rfl⟩
  have hlOval : (lO.map Subtype.val).map (EdgeDeletion.value X.toCombMap a) =
      (List.range m).map fun t => (X.toCombMap.facePerm ^ (t + 1)) a := by
    rw [hlO]
    refine List.ext_getElem ?_ fun j h1 h2 => ?_
    · simp only [List.length_map, List.length_range]
      exact (List.length_map _).trans List.length_ofFn
    · simp only [List.getElem_map, List.getElem_range]
      exact congrArg (EdgeDeletion.value X.toCombMap a)
        ((List.getElem_map _).trans (congrArg Subtype.val (List.getElem_ofFn _)))
  have hLne : ((List.range m).map fun t => (X.toCombMap.facePerm ^ (t + 1)) a) ≠ [] := by
    rw [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
    omega
  have hLnd : ((List.range m).map fun t => (X.toCombMap.facePerm ^ (t + 1)) a).Nodup := by
    refine List.Nodup.map_on ?_ List.nodup_range
    intro i hi j hj hij
    rw [List.mem_range] at hi hj
    by_contra hne
    have key : ∀ p q, p < q → q < m → (X.toCombMap.facePerm ^ (p + 1)) a =
        (X.toCombMap.facePerm ^ (q + 1)) a → False := by
      intro p q hpq hqm hpqv
      have hfix : (X.toCombMap.facePerm ^ (q - p)) a = a := by
        apply (X.toCombMap.facePerm ^ (p + 1)).injective
        rw [← Equiv.Perm.mul_apply, ← pow_add, show p + 1 + (q - p) = q + 1 by omega]
        exact hpqv.symm
      exact hne_a (q - p - 1) (by omega) (by rw [show q - p - 1 + 1 = q - p by omega]; exact hfix)
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key i j h hj hij
    · exact key j i h hi hij.symm
  have hLch : ((List.range m).map fun t => (X.toCombMap.facePerm ^ (t + 1)) a).IsChain
      (fun d e => EdgeDeletion.next X.toCombMap a d = e) := by
    rw [List.isChain_iff_getElem]
    intro j hj
    simp only [List.length_map, List.length_range] at hj
    simp only [List.getElem_map, List.getElem_range]
    exact hnext j hj
  have hLcl : ∀ u ∈ ((List.range m).map fun t => (X.toCombMap.facePerm ^ (t + 1)) a).getLast?,
      ∀ v ∈ ((List.range m).map fun t => (X.toCombMap.facePerm ^ (t + 1)) a).head?,
        EdgeDeletion.next X.toCombMap a u = v := by
    intro u hu v hv
    rw [List.getLast?_eq_getElem?, List.getElem?_map, List.length_map, List.length_range,
      List.getElem?_range (by omega), Option.map_some, Option.mem_def, Option.some.injEq] at hu
    rw [List.head?_eq_getElem?, List.getElem?_map, List.getElem?_range hm, Option.map_some,
      Option.mem_def, Option.some.injEq] at hv
    subst hu
    subst hv
    rw [show m - 1 + 1 = m by omega]
    exact hlast
  have hO : (component X.toCombMap a hface hstart).IsFaceCycle lO :=
    @isFaceCycle_of_val (EdgeDeletion.toCombMap X.toCombMap a) (Side X.toCombMap a hface hstart)
      (side_alpha X.toCombMap a hface hstart) (side_sigma X.toCombMap a hface hstart) lO
      (EdgeDeletion.isFaceCycle_of_map_value X.toCombMap a hlOval hLne hLnd hLch hLcl)
  -- Labels of the component.
  obtain ⟨label, hlabel_def⟩ : ∃ label : (component X.toCombMap a hface hstart).Dart →
      RelLetter G Lambda, ∀ x, label x = X.label (EdgeDeletion.value X.toCombMap a x.1) :=
    ⟨_, fun _ => rfl⟩
  have hlabel : ∀ x, label ((component X.toCombMap a hface hstart).alpha x) =
      HullSC.RelWord.inv (label x) := by
    intro x
    rw [hlabel_def, hlabel_def]
    show X.label (EdgeDeletion.value X.toCombMap a (EdgeDeletion.alpha X.toCombMap a x.1)) = _
    rw [EdgeDeletion.alpha_val, X.label_alpha]
  -- Every other face of the component reads one.
  have htriv : ∀ (l : List (component X.toCombMap a hface hstart).Dart)
      (hl : (component X.toCombMap a hface hstart).IsFaceCycle l),
      (component X.toCombMap a hface hstart).faceOf (l.head hl.ne_nil) ≠
        (component X.toCombMap a hface hstart).faceOf (lO.head hO.ne_nil) →
      (component X.toCombMap a hface hstart).faceOf (l.head hl.ne_nil) ∉
        (∅ : Finset (component X.toCombMap a hface hstart).Face) →
      RelLetter.listVal (l.map label) = 1 := by
    intro l hl hne _
    have hlN : (EdgeDeletion.toCombMap X.toCombMap a).IsFaceCycle (l.map Subtype.val) :=
      @isFaceCycle_val (EdgeDeletion.toCombMap X.toCombMap a) (Side X.toCombMap a hface hstart)
        (side_alpha X.toCombMap a hface hstart) (side_sigma X.toCombMap a hface hstart) l hl
    have hgood : ∀ y ∈ l.map Subtype.val,
        X.toCombMap.facePerm (EdgeDeletion.value X.toCombMap a y) ≠ a ∧
          X.toCombMap.facePerm (EdgeDeletion.value X.toCombMap a y) ≠ X.toCombMap.alpha a := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      constructor
      · intro h
        have hnf : ¬ X.toCombMap.facePerm (X.toCombMap.alpha a) = X.toCombMap.alpha a := fun hfix =>
          X.toCombMap.alpha_fixedPointFree a
            (((X.toCombMap.faceOf_eq_iff _ _).mp hface).symm.eq_of_left hfix)
        have hnext1 : EdgeDeletion.next X.toCombMap a (EdgeDeletion.value X.toCombMap a z.1) =
            X.toCombMap.sigma a := by
          rw [EdgeDeletion.next, if_pos h, if_neg hnf]
          show X.toCombMap.sigma (X.toCombMap.alpha (X.toCombMap.alpha a)) = X.toCombMap.sigma a
          rw [X.toCombMap.alpha_involutive]
        have e : (EdgeDeletion.toCombMap X.toCombMap a).facePerm z.1 = near1 X.toCombMap a hface htail :=
          (EdgeDeletion.facePerm_eq_iff _ _ _ _).mpr hnext1
        have hh := Relation.EqvGen.trans _ _ _ z.2 (hfstep z.1)
        rw [e] at hh
        exact near1_not_side X.toCombMap a hface hstart htail X.planar hh
      · intro h
        have hzv : EdgeDeletion.value X.toCombMap a z.1 = (X.toCombMap.facePerm ^ m) a := by
          apply X.toCombMap.facePerm.injective
          rw [h, ← hstep, pow_succ', Equiv.Perm.mul_apply]
        have hzmem : z ∈ lO := by
          rw [hlO]
          refine List.mem_ofFn.mpr
            ⟨⟨m - 1, by omega⟩, Subtype.ext (EdgeDeletion.value_injective _ _ ?_)⟩
          show (X.toCombMap.facePerm ^ (m - 1 + 1)) a = EdgeDeletion.value X.toCombMap a z.1
          rw [hzv, show m - 1 + 1 = m by omega]
        exact hne (((hl.mem_iff z).mp hz).symm.trans ((hO.mem_iff z).mp hzmem))
    have hlM := EdgeDeletion.isFaceCycle_map_value X.toCombMap a hlN hgood
    have hhead : ((l.map Subtype.val).map (EdgeDeletion.value X.toCombMap a)).head hlM.ne_nil =
        EdgeDeletion.value X.toCombMap a (l.head hl.ne_nil).1 := by
      rw [List.head_map]
      exact congrArg (EdgeDeletion.value X.toCombMap a) (List.head_map _)
    have hpathHead : Relation.EqvGen (AvoidEdgeStep X.toCombMap a) (X.toCombMap.alpha a)
        (EdgeDeletion.value X.toCombMap a (l.head hl.ne_nil).1) :=
      Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ (Or.inl rfl))
        (eqvGen_avoid_of_eqvGen X.toCombMap a (l.head hl.ne_nil).2)
    have hFout : X.toCombMap.faceOf (EdgeDeletion.value X.toCombMap a (l.head hl.ne_nil).1) ≠
        X.outerFace := by
      intro hF
      obtain ⟨o, ho, hao⟩ := hor
      have h2 : Relation.EqvGen (AvoidEdgeStep X.toCombMap a) o
          (EdgeDeletion.value X.toCombMap a (l.head hl.ne_nil).1) :=
        AvoidEdgeStep.eqvGen_of_faceOf_eq (ho.trans hF.symm) (fun h => hout (h.trans ho))
          (fun h => hout (hface.trans (h.trans ho)))
      exact AvoidEdgeStep.not_eqvGen_alpha_of_sameFace X.toCombMap X.planar a hface
        (Relation.EqvGen.trans _ _ _ hao
          (Relation.EqvGen.trans _ _ _ h2 (Relation.EqvGen.symm _ _ hpathHead)))
    have hFcell : X.toCombMap.faceOf (EdgeDeletion.value X.toCombMap a (l.head hl.ne_nil).1) ≠
        X.toCombMap.faceOf a := by
      intro hF
      have ha : a ∈ (l.map Subtype.val).map (EdgeDeletion.value X.toCombMap a) :=
        (hlM.mem_iff a).mpr (by rw [hhead, hF])
      obtain ⟨y, -, hy⟩ := List.mem_map.mp ha
      exact EdgeDeletion.value_ne X.toCombMap a y hy
    rcases X.inner_face _ hFout with ⟨C, hC, hCf⟩ | hval
    · exact absurd (Relation.EqvGen.symm _ _ hpathHead)
        (hfree C hC (by rw [hCf]; exact hFcell) _ hCf.symm)
    · obtain ⟨k, hk, hrot⟩ := CombMap.IsFaceCycle.exists_rotate_eq
        (X.faceBoundary (X.toCombMap.faceOf
          (EdgeDeletion.value X.toCombMap a (l.head hl.ne_nil).1))).isFaceCycle
        hlM (by rw [FaceBoundary.faceOf_head, hhead])
      have hmap : l.map label =
          ((l.map Subtype.val).map (EdgeDeletion.value X.toCombMap a)).map X.label :=
        (List.map_congr_left (f := label)
          (g := (X.label ∘ EdgeDeletion.value X.toCombMap a) ∘ Subtype.val)
          fun x _ => hlabel_def x).trans
        ((List.map_map (g := X.label) (f := EdgeDeletion.value X.toCombMap a)).trans
          (List.map_map (g := X.label ∘ EdgeDeletion.value X.toCombMap a)
            (f := Subtype.val))).symm
      rw [hmap, ← hrot, List.map_rotate, HullSC.RelWord.listVal_rotate _ (by simpa using hk), hval]
      simp
  have hK := component_planar X.toCombMap a hface hstart htail X.planar
  have hprod := isRelatorProduct_of_planar (∅ : Set G) _ (component X.toCombMap a hface hstart) rfl
    hK label hlabel ∅ lO hO (by simp) (fun _ _ h => by simp at h) htriv
  rw [Finset.card_empty] at hprod
  have h1 := RelatorDefectBudget.IsRelatorProduct.eq_one_of_index_zero hprod
  have hword : lO.map label =
      dartWord X ((List.range m).map fun t => (X.toCombMap.facePerm ^ (t + 1)) a) := by
    rw [dartWord, ← hlOval]
    exact (List.map_congr_left (f := label)
      (g := (X.label ∘ EdgeDeletion.value X.toCombMap a) ∘ Subtype.val)
      fun x _ => hlabel_def x).trans
      ((List.map_map (g := X.label) (f := EdgeDeletion.value X.toCombMap a)).trans
        (List.map_map (g := X.label ∘ EdgeDeletion.value X.toCombMap a)
          (f := Subtype.val))).symm
  rwa [hword] at h1

end BridgeComponent

#audit_axioms GroupApproximation.GGT.VanKampen.BridgeComponent.isFaceCycle_val
#audit_axioms GroupApproximation.GGT.VanKampen.BridgeComponent.isFaceCycle_of_val
#audit_axioms GroupApproximation.GGT.VanKampen.BridgeComponent.listVal_pocket_eq_one

end GroupApproximation.GGT.VanKampen
