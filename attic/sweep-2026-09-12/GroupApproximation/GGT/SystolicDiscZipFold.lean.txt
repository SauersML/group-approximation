import GroupApproximation.GGT.SystolicDiscMovesCycle
import GroupApproximation.GGT.VanKampen.FoldDiagram
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# Zipping a spur by folding (HC3(d), fold case)

Let `du dv` be consecutive exterior darts of a cycle disc reading `u v u`: the dart after
`dv` is labelled like `du`.  Let `p` be the exterior dart before `du`.  When the corners
before `du` and after `dv` lie at different vertices (`¬ SameCycle σ (α p) (α dv)`), the
pair is foldable (`FoldMap.IsFoldable`): joining the two vertices and deleting the edge of
`dv` glues the two edges.  All interior faces are kept and the exterior walk loses the
spur (`CycleDisc.zip_fold`).

* `faceCycle_three_apply`: a face cycle of three darts reads the face rotation.
* `CycleDisc.isFaceCycle_tri`: an interior dart heads a face cycle of three darts.
* `CycleDisc.joined_lab_sigma`: labels are constant along the joined vertex rotation.
* `CycleDisc.map_lab_foldList`: transport along the fold keeps the labels.
-/

namespace GroupApproximation.Systolic

open GGT.VanKampen

universe u

variable {V : Type u} {X : TriangleComplex V}

/-- A face cycle of three darts reads the face rotation from its head. -/
theorem faceCycle_three_apply {M : CombMap.{0}} {a b c : M.Dart} (h : M.IsFaceCycle [a, b, c]) :
    M.facePerm a = b ∧ (M.facePerm ^ 2) a = c ∧ (M.facePerm ^ 3) a = a := by
  have hab : M.facePerm a = b := (List.isChain_cons_cons.mp h.chain).1
  have hbc : M.facePerm b = c :=
    (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp h.chain).2).1
  have hca : M.facePerm c = a := h.closes
  refine ⟨hab, ?_, ?_⟩
  · rw [perm_pow_two_apply, hab, hbc]
  · rw [perm_pow_three_apply, hab, hbc, hca]

namespace CycleDisc

variable (D : CycleDisc X)

/-- **An interior dart heads a triangle face cycle.** -/
theorem isFaceCycle_tri {y : D.map.Dart} (hy : y ∉ D.cyc) :
    D.map.IsFaceCycle [y, D.map.facePerm y, (D.map.facePerm ^ 2) y] := by
  obtain ⟨h3, ht⟩ := D.tri y hy
  have hadj := X.tri_adj ht
  have h01 : y ≠ D.map.facePerm y := fun h => hadj.1.ne (congrArg D.lab h)
  have h02 : y ≠ (D.map.facePerm ^ 2) y := fun h => hadj.2.2.ne (congrArg D.lab h)
  have h12 : D.map.facePerm y ≠ (D.map.facePerm ^ 2) y := fun h => hadj.2.1.ne (congrArg D.lab h)
  refine ⟨List.cons_ne_nil _ _, ?_, ?_, ?_⟩
  · refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨h01, h02⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact h12
  · exact List.isChain_cons_cons.mpr ⟨rfl, List.isChain_cons_cons.mpr
      ⟨(perm_pow_two_apply _ _).symm, List.isChain_singleton _⟩⟩
  · show D.map.facePerm ((D.map.facePerm ^ 2) y) = y
    rw [perm_pow_two_apply, ← perm_pow_three_apply]
    exact h3

/-- **Labels along the joined vertex rotation.**  Joining the corners before `du` and after
`dv` keeps the labels constant along vertex rotation, since both corners read `u`. -/
theorem joined_lab_sigma [DecidableEq D.map.Dart] {p du dv : D.map.Dart}
    (hprev : D.map.facePerm p = du) (hlab : D.lab (D.map.facePerm dv) = D.lab du)
    (y : D.map.Dart) :
    D.lab ((FoldMap.joined D.map p dv).sigma y) = D.lab y := by
  have hp : D.lab (D.map.alpha p) = D.lab du := by
    rw [← D.lab_sigma (D.map.alpha p)]
    exact congrArg D.lab hprev
  have hv : D.lab (D.map.alpha dv) = D.lab du := by
    rw [← D.lab_sigma (D.map.alpha dv)]
    exact hlab
  show D.lab (D.map.sigma (Equiv.swap (D.map.alpha p) (D.map.alpha dv) y)) = D.lab y
  rw [D.lab_sigma]
  by_cases h1 : y = D.map.alpha p
  · rw [h1, Equiv.swap_apply_left, hv, hp]
  · by_cases h2 : y = D.map.alpha dv
    · rw [h2, Equiv.swap_apply_right, hv, hp]
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- An exterior dart off the folded pair transports to a dart with the same label. -/
theorem foldImage_lab [DecidableEq D.map.Dart] {du dv : D.map.Dart}
    (hv : D.lab (D.map.alpha dv) = D.lab du) {z : D.map.Dart} (hzd : z ≠ du) (hze : z ≠ dv) :
    ∃ w, FoldMap.foldImage D.map du dv z = some w ∧ D.lab w = D.lab z := by
  have hc : ¬ (z = du ∨ z = dv) := fun h' => h'.elim hzd hze
  by_cases hzα : z = D.map.alpha dv
  · refine ⟨du, ?_, ?_⟩
    · unfold FoldMap.foldImage
      rw [if_neg hc, if_pos hzα]
    · rw [hzα, hv]
  · refine ⟨z, ?_, rfl⟩
    unfold FoldMap.foldImage
    rw [if_neg hc, if_neg hzα]

/-- **Transport along the fold keeps the labels** of a list avoiding the folded pair. -/
theorem map_lab_foldList [DecidableEq D.map.Dart] {p du dv : D.map.Dart}
    (h : FoldMap.IsFoldable D.map p du dv) (hv : D.lab (D.map.alpha dv) = D.lab du)
    {l : List D.map.Dart} (hd : du ∉ l) (he : dv ∉ l) :
    (FoldMap.foldList D.map du dv l).map D.lab = l.map D.lab := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      have hd' : du ∉ l := fun hm => hd (List.mem_cons_of_mem x hm)
      have he' : dv ∉ l := fun hm => he (List.mem_cons_of_mem x hm)
      have hxd : x ≠ du := fun hx => hd (hx ▸ List.mem_cons_self)
      have hxe : x ≠ dv := fun hx => he (hx ▸ List.mem_cons_self)
      by_cases hxα : x = D.map.alpha dv
      · subst hxα
        rw [FoldMap.foldList_cons_alpha (fun h' => h.ne_alpha_next h'.symm)
          (D.map.alpha_fixedPointFree dv), List.map_cons, List.map_cons, ih hd' he', hv]
      · rw [FoldMap.foldList_cons_of_ne hxd hxe hxα, List.map_cons, List.map_cons, ih hd' he']

/-- Labels on the folded map. -/
def foldLab [DecidableEq D.map.Dart] (p dv : D.map.Dart)
    (x : (FoldMap.toCombMap D.map p dv).Dart) : V :=
  D.lab (EdgeDeletion.value (FoldMap.joined D.map p dv) dv x)

theorem foldLab_sigma [DecidableEq D.map.Dart] {p du dv : D.map.Dart}
    (hprev : D.map.facePerm p = du) (hlab : D.lab (D.map.facePerm dv) = D.lab du)
    (x : (FoldMap.toCombMap D.map p dv).Dart) :
    D.foldLab p dv ((FoldMap.toCombMap D.map p dv).sigma x) = D.foldLab p dv x := by
  have hv := (EdgeDeletion.vertexOf_eq_iff (FoldMap.joined D.map p dv) dv _ x).mp
    (CombMap.vertexOf_sigma (FoldMap.toCombMap D.map p dv) x)
  rw [CombMap.vertexOf_eq_iff] at hv
  exact OrbitClassifier.eq_of_sameCycle _ D.lab (D.joined_lab_sigma hprev hlab) hv

theorem foldLab_adj [DecidableEq D.map.Dart] (p dv : D.map.Dart)
    (x : (FoldMap.toCombMap D.map p dv).Dart) :
    X.G.Adj (D.foldLab p dv x) (D.foldLab p dv ((FoldMap.toCombMap D.map p dv).alpha x)) := by
  show X.G.Adj (D.lab (EdgeDeletion.value (FoldMap.joined D.map p dv) dv x))
    (D.lab (EdgeDeletion.value (FoldMap.joined D.map p dv) dv
      (EdgeDeletion.alpha (FoldMap.joined D.map p dv) dv x)))
  rw [EdgeDeletion.alpha_val]
  exact D.adj _

/-- **HC3(d), fold case: zipping a spur whose two ends lie at different vertices.**  The
exterior walk `s ++ du :: dv :: t`, read `u v u` at the spur, becomes `s ++ t`. -/
theorem zip_fold {s t : List D.map.Dart} {p du dv : D.map.Dart}
    (hcyc : D.cyc = s ++ du :: dv :: t) (hprev : D.map.facePerm p = du)
    (hlab : D.lab (D.map.facePerm dv) = D.lab du) (hst : s ++ t ≠ [])
    (hpinch : ¬ D.map.sigma.SameCycle (D.map.alpha p) (D.map.alpha dv)) :
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
  have hnotspur : dv ≠ D.map.alpha du := by
    intro h'
    apply hpinch
    have h2 : D.map.alpha dv = D.map.sigma (D.map.alpha p) := by
      rw [h', D.map.alpha_involutive du]
      exact hprev.symm
    rw [h2]
    exact (Equiv.Perm.SameCycle.rfl.apply_left).symm
  have h : FoldMap.IsFoldable D.map p du dv := ⟨hprev, hnext, hpe, hnotspur, hpinch⟩
  have hv : D.lab (D.map.alpha dv) = D.lab du := by
    rw [← D.lab_sigma (D.map.alpha dv)]
    exact hlab
  have hnd : (s ++ du :: dv :: t).Nodup := by
    rw [← hcyc]
    exact D.isFaceCycle.nodup
  have hds : du ∉ s := fun hm => (List.nodup_append.mp hnd).2.2 _ hm _ List.mem_cons_self rfl
  have hes : dv ∉ s := fun hm =>
    (List.nodup_append.mp hnd).2.2 _ hm _ (List.mem_cons_of_mem du List.mem_cons_self) rfl
  have hdt : du ∉ t := fun hm =>
    (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 (List.mem_cons_of_mem dv hm)
  have het : dv ∉ t := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).2).1
  have hdu_cyc : du ∈ D.cyc := by
    rw [hcyc]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hdv_cyc : dv ∈ D.cyc := by
    rw [hcyc]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem du List.mem_cons_self))
  obtain ⟨l', hl'⟩ := FoldMap.exists_lift_foldList h D.cyc
  have hmap : l'.map (D.foldLab p dv) = s.map D.lab ++ t.map D.lab := by
    have h1 : l'.map (D.foldLab p dv) = (FoldMap.foldList D.map du dv D.cyc).map D.lab := by
      rw [← hl', List.map_map]
      rfl
    rw [h1, hcyc, FoldMap.foldList_append, FoldMap.foldList_cons_d, FoldMap.foldList_cons_e,
      List.map_append, D.map_lab_foldList h hv hds hes, D.map_lab_foldList h hv hdt het]
  refine ⟨{ map := FoldMap.toCombMap D.map p dv
            planar := FoldMap.planar D.planar h
            lab := D.foldLab p dv
            lab_sigma := D.foldLab_sigma hprev hlab
            adj := D.foldLab_adj p dv
            cyc := l'
            isFaceCycle := FoldMap.isFaceCycle_of_foldList h D.isFaceCycle hl'
            tri := ?_ }, hmap⟩
  intro x hx
  have hxv : EdgeDeletion.value (FoldMap.joined D.map p dv) dv x ∉
      FoldMap.foldList D.map du dv D.cyc := by
    intro hm
    rw [← hl'] at hm
    obtain ⟨x', hx', hxx'⟩ := List.mem_map.mp hm
    rw [EdgeDeletion.value_injective (FoldMap.joined D.map p dv) dv hxx'] at hx'
    exact hx hx'
  -- the dart of the old map that transports to `x`
  obtain ⟨y, hy, hyx⟩ : ∃ y, y ∉ D.cyc ∧ FoldMap.foldImage D.map du dv y =
      some (EdgeDeletion.value (FoldMap.joined D.map p dv) dv x) := by
    by_cases hxd : EdgeDeletion.value (FoldMap.joined D.map p dv) dv x = du
    · have hαd : D.map.alpha dv ≠ du := fun h' => h.ne_alpha_next h'.symm
      have hc1 : ¬ (D.map.alpha dv = du ∨ D.map.alpha dv = dv) := fun h' =>
        h'.elim hαd (D.map.alpha_fixedPointFree dv)
      have hc2 : D.map.alpha dv = D.map.alpha dv := rfl
      have himg : FoldMap.foldImage D.map du dv (D.map.alpha dv) = some du := by
        unfold FoldMap.foldImage
        rw [if_neg hc1, if_pos hc2]
      refine ⟨D.map.alpha dv, fun hm => hxv ?_, by rw [himg, hxd]⟩
      rw [hxd]
      exact List.mem_filterMap.mpr ⟨D.map.alpha dv, hm, himg⟩
    · have hxe : EdgeDeletion.value (FoldMap.joined D.map p dv) dv x ≠ dv :=
        EdgeDeletion.value_ne (FoldMap.joined D.map p dv) dv x
      have hxα : EdgeDeletion.value (FoldMap.joined D.map p dv) dv x ≠ D.map.alpha dv :=
        EdgeDeletion.value_ne_reverse (FoldMap.joined D.map p dv) dv x
      have himg : FoldMap.foldImage D.map du dv (EdgeDeletion.value (FoldMap.joined D.map p dv) dv x) =
          some (EdgeDeletion.value (FoldMap.joined D.map p dv) dv x) := by
        have hc1 : ¬ (EdgeDeletion.value (FoldMap.joined D.map p dv) dv x = du ∨
            EdgeDeletion.value (FoldMap.joined D.map p dv) dv x = dv) := fun h' => h'.elim hxd hxe
        unfold FoldMap.foldImage
        rw [if_neg hc1, if_neg hxα]
      exact ⟨_, fun hm => hxv (List.mem_filterMap.mpr ⟨_, hm, himg⟩), himg⟩
  have hy1 : D.map.facePerm y ∉ D.cyc := D.facePerm_not_mem hy
  have hy2 : (D.map.facePerm ^ 2) y ∉ D.cyc := by
    rw [perm_pow_two_apply]
    exact D.facePerm_not_mem hy1
  have hne : ∀ {z : D.map.Dart}, z ∉ D.cyc → z ≠ du ∧ z ≠ dv := fun hz =>
    ⟨fun h' => hz (by rw [h']; exact hdu_cyc), fun h' => hz (by rw [h']; exact hdv_cyc)⟩
  obtain ⟨w0, hw0, hl0⟩ := D.foldImage_lab hv (hne hy).1 (hne hy).2
  obtain ⟨w1, hw1, hl1⟩ := D.foldImage_lab hv (hne hy1).1 (hne hy1).2
  obtain ⟨w2, hw2, hl2⟩ := D.foldImage_lab hv (hne hy2).1 (hne hy2).2
  have hw0x : w0 = EdgeDeletion.value (FoldMap.joined D.map p dv) dv x :=
    Option.some.inj (hw0.symm.trans hyx)
  have hfl : FoldMap.foldList D.map du dv [y, D.map.facePerm y, (D.map.facePerm ^ 2) y] =
      [EdgeDeletion.value (FoldMap.joined D.map p dv) dv x, w1, w2] := by
    unfold FoldMap.foldList
    rw [List.filterMap_cons_some hyx, List.filterMap_cons_some hw1, List.filterMap_cons_some hw2,
      List.filterMap_nil]
  have hw1m := FoldMap.foldList_avoid h [y, D.map.facePerm y, (D.map.facePerm ^ 2) y] w1
    (by rw [hfl]; simp)
  have hw2m := FoldMap.foldList_avoid h [y, D.map.facePerm y, (D.map.facePerm ^ 2) y] w2
    (by rw [hfl]; simp)
  have hlB : [x, EdgeDeletion.ofValue (FoldMap.joined D.map p dv) dv w1 hw1m.1 hw1m.2,
      EdgeDeletion.ofValue (FoldMap.joined D.map p dv) dv w2 hw2m.1 hw2m.2].map
        (EdgeDeletion.value (FoldMap.joined D.map p dv) dv) =
      FoldMap.foldList D.map du dv [y, D.map.facePerm y, (D.map.facePerm ^ 2) y] := by
    rw [hfl]
    rfl
  obtain ⟨h1, h2, h3⟩ := faceCycle_three_apply (FoldMap.isFaceCycle_of_foldList h (D.isFaceCycle_tri hy) hlB)
  refine ⟨h3, ?_⟩
  rw [h1, h2]
  show X.Tri (D.lab (EdgeDeletion.value (FoldMap.joined D.map p dv) dv x)) (D.lab w1) (D.lab w2)
  rw [hl1, hl2, ← hw0x, hl0]
  exact (D.tri y hy).2

end CycleDisc

end GroupApproximation.Systolic
