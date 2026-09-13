import GroupApproximation.GGT.SystolicDiscZipFold
import GroupApproximation.GGT.VanKampen.PinchLemma
import GroupApproximation.GGT.VanKampen.CombMapInvariantRestrict
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# Zipping a spur whose ends meet (HC3(d), pinch case)

Let `du dv` be consecutive exterior darts of a cycle disc reading `u v u`, and `p` the exterior
dart before `du`.  Suppose the corners before `du` and after `dv` lie at one vertex
(`SameCycle σ (α p) (α dv)`); this includes the spur `dv = alpha du`.  Splitting that vertex
(`FoldMap.joined`) raises the Euler characteristic to `4` (`PinchLemma.split_euler`), and `du` does
not reach `p` in the split map (`PinchLemma.not_reach_p`).  The part reached from `p` and the part
reached from `du` are connected, so both are planar (`CombMap.restrict_planar_of_euler_four`).

The part reached from `p` is a cycle disc (`CycleDisc.zip_pinch`).  Its exterior face is the rest
`t ++ s` of the old exterior face (`PinchLemma.split_isFaceCycle_rest`), rotated to read `s ++ t`.
Its other darts are off the old exterior cycle, where the split map rotates faces as the old map
does, so its other faces are old interior triangles.

* `isFaceCycle_of_map_injective`: face cycles pull back along an injective map commuting with face
  rotation.
* `exists_map_val_eq`: a list inside a set lifts to the subtype.
* `CycleDisc.pinchMap`: the part of the split map reached from `p`.
* `zipPinchStatement`: HC3(d), pinch case.
-/

namespace GroupApproximation.Systolic

open GGT.VanKampen

universe u

variable {V : Type u} {X : TriangleComplex V}

/-- **Face cycles pull back** along an injective map of darts commuting with face rotation. -/
theorem isFaceCycle_of_map_injective {M N : CombMap.{u}} (f : N.Dart → M.Dart)
    (hf : Function.Injective f) (hcomm : ∀ x, f (N.facePerm x) = M.facePerm (f x))
    {l' : List N.Dart} {l : List M.Dart} (hmap : l'.map f = l) (hl : M.IsFaceCycle l) :
    N.IsFaceCycle l' := by
  subst hmap
  have hne : l' ≠ [] := by
    rintro rfl
    exact hl.ne_nil rfl
  refine ⟨hne, List.Nodup.of_map f hl.nodup, ?_, ?_⟩
  · exact ((List.isChain_map f).mp hl.chain).imp_of_mem_imp
      fun a b _ _ (h : M.facePerm (f a) = f b) => hf (by rw [hcomm, h])
  · apply hf
    have hc := hl.closes
    rw [List.getLast_map, List.head_map] at hc
    rw [hcomm]
    exact hc

/-- A list whose entries satisfy a predicate lifts to the subtype. -/
theorem exists_map_val_eq {α : Type*} {S : α → Prop} :
    ∀ l : List α, (∀ x ∈ l, S x) → ∃ l' : List {x // S x}, l'.map Subtype.val = l
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨l', hl'⟩ := exists_map_val_eq l fun x hx => h x (List.mem_cons_of_mem a hx)
    exact ⟨⟨a, h a List.mem_cons_self⟩ :: l', by rw [List.map_cons, hl']⟩

namespace CycleDisc

variable (D : CycleDisc X)

/-- The darts of the split map reached from `p`. -/
def pinchSide [DecidableEq D.map.Dart] (p dv x : D.map.Dart) : Prop :=
  Relation.EqvGen (FoldMap.joined D.map p dv).Adjacent p x

theorem pinchSide_alpha [DecidableEq D.map.Dart] (p dv x : D.map.Dart) :
    D.pinchSide p dv ((FoldMap.joined D.map p dv).alpha x) ↔ D.pinchSide p dv x :=
  ⟨fun h => Relation.EqvGen.trans _ _ _ h
      (Relation.EqvGen.rel _ _ (Or.inl ((FoldMap.joined D.map p dv).alpha_involutive x))),
    fun h => Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.rel _ _ (Or.inl rfl))⟩

theorem pinchSide_sigma [DecidableEq D.map.Dart] (p dv x : D.map.Dart) :
    D.pinchSide p dv ((FoldMap.joined D.map p dv).sigma x) ↔ D.pinchSide p dv x :=
  ⟨fun h => Relation.EqvGen.trans _ _ _ h
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inr rfl))),
    fun h => Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.rel _ _ (Or.inr rfl))⟩

/-- The part of the split map reached from `p`. -/
noncomputable abbrev pinchMap [DecidableEq D.map.Dart] (p dv : D.map.Dart) : CombMap.{0} :=
  (FoldMap.joined D.map p dv).restrict (D.pinchSide p dv) (D.pinchSide_alpha p dv)
    (D.pinchSide_sigma p dv)

/-- **HC3(d), pinch case: zipping a spur whose two ends lie at one vertex.**  The exterior walk
`s ++ du :: dv :: t`, read `u v u` at the spur, becomes `s ++ t`. -/
theorem zip_pinch {s t : List D.map.Dart} {p du dv : D.map.Dart}
    (hcyc : D.cyc = s ++ du :: dv :: t) (hprev : D.map.facePerm p = du)
    (hlab : D.lab (D.map.facePerm dv) = D.lab du) (hst : s ++ t ≠ [])
    (hpinch : D.map.sigma.SameCycle (D.map.alpha p) (D.map.alpha dv)) :
    ∃ D' : CycleDisc X, D'.cyc.map D'.lab = s.map D.lab ++ t.map D.lab := by
  classical
  have hR : D.map.IsFaceCycle (du :: dv :: (t ++ s)) := by
    have hr := D.isFaceCycle.rotate s.length
    rw [hcyc, List.rotate_append_length_eq] at hr
    exact hr
  have hnext : D.map.facePerm du = dv := (List.isChain_cons_cons.mp hR.chain).1
  have hdv_mem : dv ∉ t ++ s := (List.nodup_cons.mp (List.nodup_cons.mp hR.nodup).2).1
  have hts : t ++ s ≠ [] := fun h' =>
    hst (List.append_eq_nil_iff.mpr ⟨(List.append_eq_nil_iff.mp h').2, (List.append_eq_nil_iff.mp h').1⟩)
  have hlast : (du :: dv :: (t ++ s)).getLast hR.ne_nil = (t ++ s).getLast hts := by
    rw [List.getLast_cons_cons, List.getLast_cons hts]
  have hpL : p ∈ t ++ s := by
    have hc : D.map.facePerm ((t ++ s).getLast hts) = D.map.facePerm p := by
      rw [← hlast, hprev]
      exact hR.closes
    rw [← D.map.facePerm.injective hc]
    exact List.getLast_mem hts
  have hpe : p ≠ dv := fun h' => hdv_mem (by rw [← h']; exact hpL)
  have hde : du ≠ dv := fun h' =>
    (List.nodup_cons.mp hR.nodup).1 (by rw [h']; exact List.mem_cons_self)
  have hdp : du ≠ p := by
    intro h'
    apply hde
    rw [← hnext, h', hprev, ← h']
  have hp_cyc : p ∈ D.cyc := by
    rw [hcyc]
    rcases List.mem_append.mp hpL with h' | h'
    · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem du (List.mem_cons_of_mem dv h')))
    · exact List.mem_append.mpr (Or.inl h')
  have hdv_cyc : dv ∈ D.cyc := by
    rw [hcyc]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem du List.mem_cons_self))
  have hface : D.map.faceOf p = D.map.faceOf dv :=
    ((D.isFaceCycle.mem_iff p).mp hp_cyc).trans ((D.isFaceCycle.mem_iff dv).mp hdv_cyc).symm
  have hnot := PinchLemma.not_reach_p D.planar hprev hnext hde hdp hpe hface hpinch
  -- both parts of the split map are connected, so the part reached from `p` is planar
  have hplanar : (D.pinchMap p dv).IsPlanar :=
    CombMap.restrict_planar_of_euler_four (FoldMap.joined D.map p dv) (D.pinchSide p dv)
      (D.pinchSide_alpha p dv) (D.pinchSide_sigma p dv)
      (PinchLemma.split_euler D.planar hpe hface hpinch)
      (CombMap.restrict_connected (FoldMap.joined D.map p dv) (D.pinchSide p dv)
        (D.pinchSide_alpha p dv) (D.pinchSide_sigma p dv) (x₀ := p) (Relation.EqvGen.refl p)
        fun _ hx => hx)
      (CombMap.restrict_connected (FoldMap.joined D.map p dv) (fun x => ¬ D.pinchSide p dv x)
        ((FoldMap.joined D.map p dv).compl_alpha (D.pinchSide p dv) (D.pinchSide_alpha p dv))
        ((FoldMap.joined D.map p dv).compl_sigma (D.pinchSide p dv) (D.pinchSide_sigma p dv))
        (x₀ := du) (fun h' => hnot (Relation.EqvGen.symm _ _ h'))
        fun x hx => (PinchLemma.reach_or_reach D.planar.1 hprev hnext hde hdp x).resolve_right hx)
  -- the rest of the exterior face lies in that part
  have hJR := PinchLemma.split_isFaceCycle_rest hprev hpe hR
  have hside : ∀ x ∈ t ++ s, D.pinchSide p dv x := fun x hx =>
    PinchLemma.eqvGen_of_faceOf_eq (((hJR.mem_iff p).mp hpL).trans ((hJR.mem_iff x).mp hx).symm)
  obtain ⟨l', hl'⟩ := exists_map_val_eq (S := D.pinchSide p dv) (t ++ s) hside
  have hl'fc : (D.pinchMap p dv).IsFaceCycle l' :=
    isFaceCycle_of_map_injective (M := FoldMap.joined D.map p dv) (N := D.pinchMap p dv)
      Subtype.val Subtype.val_injective (fun _ => rfl) hl' hJR
  -- off the old exterior cycle the split map rotates faces as the old map does
  have hJF : ∀ z, z ∉ D.cyc → (FoldMap.joined D.map p dv).facePerm z = D.map.facePerm z := by
    intro z hz
    rw [FoldMap.joined_facePerm_apply, Equiv.swap_apply_of_ne_of_ne
      (fun h' => hz (by rw [h']; exact hp_cyc)) (fun h' => hz (by rw [h']; exact hdv_cyc))]
  refine ⟨{ map := D.pinchMap p dv
            planar := hplanar
            lab := D.lab ∘ Subtype.val
            lab_sigma := fun x => D.joined_lab_sigma hprev hlab x.1
            adj := fun x => D.adj x.1
            cyc := l'.rotate t.length
            isFaceCycle := hl'fc.rotate t.length
            tri := ?_ }, ?_⟩
  · intro x hx
    have hxl : x ∉ l' := fun hm => hx (List.mem_rotate.mpr hm)
    have hts_mem : ∀ z : (D.pinchMap p dv).Dart, z.1 ∈ t ++ s → z ∈ l' := by
      intro z hz
      rw [← hl'] at hz
      obtain ⟨y, hyl, hyz⟩ := List.mem_map.mp hz
      obtain rfl : y = z := Subtype.ext hyz
      exact hyl
    -- `x` is off the old exterior cycle: `du` and `dv` are not reached from `p`
    have hy : x.1 ∉ D.cyc := by
      intro hm
      have hx2 : D.pinchSide p dv x.1 := x.2
      rw [hcyc] at hm
      rcases List.mem_append.mp hm with h' | h'
      · exact hxl (hts_mem x (List.mem_append.mpr (Or.inr h')))
      · rcases List.mem_cons.mp h' with h'' | h''
        · rw [h''] at hx2
          exact hnot (Relation.EqvGen.symm _ _ hx2)
        · rcases List.mem_cons.mp h'' with h3 | h3
          · rw [h3] at hx2
            have hdu : D.pinchSide p dv du :=
              (CombMap.facePerm_invariant (FoldMap.joined D.map p dv) (D.pinchSide p dv)
                (D.pinchSide_alpha p dv) (D.pinchSide_sigma p dv) du).mp
                (by rw [PinchLemma.split_facePerm_d hnext hde hdp]; exact hx2)
            exact hnot (Relation.EqvGen.symm _ _ hdu)
          · exact hxl (hts_mem x (List.mem_append.mpr (Or.inl h3)))
    obtain ⟨h3, htri⟩ := D.tri x.1 hy
    have hy1 : D.map.facePerm x.1 ∉ D.cyc := D.facePerm_not_mem hy
    have hy2 : D.map.facePerm (D.map.facePerm x.1) ∉ D.cyc := D.facePerm_not_mem hy1
    have e1 : ((D.pinchMap p dv).facePerm x).1 = D.map.facePerm x.1 := hJF x.1 hy
    have e2 : ((D.pinchMap p dv).facePerm ((D.pinchMap p dv).facePerm x)).1 =
        D.map.facePerm (D.map.facePerm x.1) :=
      (congrArg (FoldMap.joined D.map p dv).facePerm e1).trans (hJF _ hy1)
    have e3 : ((D.pinchMap p dv).facePerm ((D.pinchMap p dv).facePerm
        ((D.pinchMap p dv).facePerm x))).1 =
        D.map.facePerm (D.map.facePerm (D.map.facePerm x.1)) :=
      (congrArg (FoldMap.joined D.map p dv).facePerm e2).trans (hJF _ hy2)
    refine ⟨Subtype.ext ((congrArg Subtype.val (perm_pow_three_apply (D.pinchMap p dv).facePerm x)).trans
      (e3.trans ((perm_pow_three_apply D.map.facePerm x.1).symm.trans h3))), ?_⟩
    have hb : D.lab ((D.pinchMap p dv).facePerm x).1 = D.lab (D.map.facePerm x.1) :=
      congrArg D.lab e1
    have hc : D.lab (((D.pinchMap p dv).facePerm ^ 2) x).1 = D.lab ((D.map.facePerm ^ 2) x.1) :=
      congrArg D.lab ((congrArg Subtype.val (perm_pow_two_apply (D.pinchMap p dv).facePerm x)).trans
        (e2.trans (perm_pow_two_apply D.map.facePerm x.1).symm))
    show X.Tri (D.lab x.1) (D.lab ((D.pinchMap p dv).facePerm x).1)
      (D.lab (((D.pinchMap p dv).facePerm ^ 2) x).1)
    rw [hb, hc]
    exact htri
  · show (l'.rotate t.length).map (D.lab ∘ Subtype.val) = s.map D.lab ++ t.map D.lab
    have hmap : l'.map (D.lab ∘ Subtype.val) = t.map D.lab ++ s.map D.lab := by
      rw [← List.map_append, ← hl', List.map_map]
    have hlen : (t.map D.lab).length = t.length := by simp only [List.length_map]
    rw [List.map_rotate, hmap, ← hlen, List.rotate_append_length_eq]

end CycleDisc

/-- **HC3(d), pinch case**, for every triangle complex. -/
theorem zipPinchStatement (X : TriangleComplex V) : ZipPinchStatement X :=
  fun D _ _ _ _ _ hcyc hprev hlab hst hpinch => D.zip_pinch hcyc hprev hlab hst hpinch

end GroupApproximation.Systolic

#audit_axioms GroupApproximation.Systolic.isFaceCycle_of_map_injective
#audit_axioms GroupApproximation.Systolic.exists_map_val_eq
#audit_axioms GroupApproximation.Systolic.CycleDisc.zip_pinch
#audit_axioms GroupApproximation.Systolic.zipPinchStatement
