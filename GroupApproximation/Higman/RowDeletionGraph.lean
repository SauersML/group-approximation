import GroupApproximation.Higman.RowDeletionBenign

/-!
# Deletion graphs for the two remaining row kernels

The kernel of a deletion retraction on the countable row is cut out by its
graph.  The graph itself splits generator-by-generator into two pieces: the
deleted row generators enter the first factor, while the retained generators
enter diagonally.  Thus benignness of the two coordinate subgroups gives
benignness of the deletion kernel.

For deletion at zero the retained subgroup is the join of the positive and
negative half rows.  For parity deletion the retained and deleted coordinate
subgroups are the images of the row under `Row.xi 0` and `Row.xi 1`.
-/

namespace GroupApproximation
namespace Higman

noncomputable section

namespace RowDeletionGraph

open Row

/-- The free subgroup on the row indices satisfying `p`. -/
def indexSub (p : ℤ → Prop) : Subgroup (FreeGroup ℤ) :=
  Subgroup.closure (FreeGroup.of '' {i : ℤ | p i})

/-- The diagonal embedding of the rank-two row carrier. -/
def diagHom : F₀ →* F₀ × F₀ :=
  (MonoidHom.id F₀).prod (MonoidHom.id F₀)

theorem diagHom_injective : Function.Injective diagHom := by
  intro x y h
  exact congrArg Prod.fst h

/-- The graph of deletion, after spelling both coordinates in the rank-two row
carrier. -/
def deletionGraphHom (p : ℤ → Prop) [DecidablePred p] :
    FreeGroup ℤ →* F₀ × F₀ :=
  Row.basisHom.prod (Row.basisHom.comp (Split.killOn p))

@[simp] theorem deletionGraphHom_of (p : ℤ → Prop) [DecidablePred p]
    (i : ℤ) :
    deletionGraphHom p (FreeGroup.of i) =
      if p i then (Row.row i, Row.row i) else (Row.row i, 1) := by
  by_cases hi : p i
  · simp [deletionGraphHom, Split.killOn_of, hi]
  · simp [deletionGraphHom, Split.killOn_of, hi]

theorem killOn_eq_self_of_mem_indexSub (p : ℤ → Prop) [DecidablePred p]
    {w : FreeGroup ℤ} (hw : w ∈ indexSub p) : Split.killOn p w = w := by
  refine Subgroup.closure_induction (p := fun z _ => Split.killOn p z = z)
    ?_ (map_one _) ?_ ?_ hw
  · rintro _ ⟨i, hi, rfl⟩
    change p i at hi
    simp [Split.killOn_of, hi]
  · intro x y _ _ hx hy
    rw [map_mul, hx, hy]
  · intro x _ hx
    rw [map_inv, hx]

theorem top_eq_indexSub_sup (p : ℤ → Prop) :
    (⊤ : Subgroup (FreeGroup ℤ)) = indexSub p ⊔ indexSub (fun i => ¬ p i) := by
  apply le_antisymm
  · rw [← FreeGroup.closure_range_of ℤ]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    by_cases hi : p i
    · exact Subgroup.mem_sup_left
        (Subgroup.subset_closure ⟨i, hi, rfl⟩)
    · exact Subgroup.mem_sup_right
        (Subgroup.subset_closure ⟨i, hi, rfl⟩)
  · exact le_top

theorem map_indexSub_deletionGraph_keep (p : ℤ → Prop) [DecidablePred p] :
    (indexSub p).map (deletionGraphHom p) =
      ((indexSub p).map Row.basisHom).map diagHom := by
  apply le_antisymm
  · rintro x ⟨w, hw, rfl⟩
    refine Subgroup.mem_map.mpr ⟨Row.basisHom w,
      Subgroup.mem_map.mpr ⟨w, hw, rfl⟩, ?_⟩
    simp only [diagHom, deletionGraphHom, MonoidHom.prod_apply,
      MonoidHom.id_apply, MonoidHom.comp_apply]
    rw [killOn_eq_self_of_mem_indexSub p hw]
  · rintro x ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    refine Subgroup.mem_map.mpr ⟨w, hw, ?_⟩
    simp only [diagHom, deletionGraphHom, MonoidHom.prod_apply,
      MonoidHom.id_apply, MonoidHom.comp_apply]
    rw [killOn_eq_self_of_mem_indexSub p hw]

theorem map_indexSub_deletionGraph_drop (p : ℤ → Prop) [DecidablePred p] :
    (indexSub (fun i => ¬ p i)).map (deletionGraphHom p) =
      ((indexSub (fun i => ¬ p i)).map Row.basisHom).map
        (MonoidHom.inl F₀ F₀) := by
  apply le_antisymm
  · rintro x ⟨w, hw, rfl⟩
    refine Subgroup.mem_map.mpr ⟨Row.basisHom w,
      Subgroup.mem_map.mpr ⟨w, hw, rfl⟩, ?_⟩
    simp only [deletionGraphHom, MonoidHom.prod_apply, MonoidHom.comp_apply,
      MonoidHom.inl_apply]
    rw [Split.killOn_eq_one_of_mem_closure hw, map_one]
  · rintro x ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    refine Subgroup.mem_map.mpr ⟨w, hw, ?_⟩
    simp only [deletionGraphHom, MonoidHom.prod_apply, MonoidHom.comp_apply,
      MonoidHom.inl_apply]
    rw [Split.killOn_eq_one_of_mem_closure hw, map_one]

theorem range_deletionGraphHom (p : ℤ → Prop) [DecidablePred p] :
    (deletionGraphHom p).range =
      (indexSub p).map (deletionGraphHom p) ⊔
        (indexSub (fun i => ¬ p i)).map (deletionGraphHom p) := by
  rw [MonoidHom.range_eq_map, top_eq_indexSub_sup p, Subgroup.map_sup]

/-- Pulling the deletion graph back along the first-factor inclusion cuts out
exactly the image of the deletion kernel. -/
theorem comap_range_deletionGraphHom (p : ℤ → Prop) [DecidablePred p] :
    (deletionGraphHom p).range.comap (MonoidHom.inl F₀ F₀) =
      (MonoidHom.ker (Split.killOn p)).map Row.basisHom := by
  apply le_antisymm
  · intro x hx
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (Subgroup.mem_comap.mp hx)
    have hfst : Row.basisHom w = x := congrArg Prod.fst hw
    have hsnd : Row.basisHom (Split.killOn p w) = 1 := by
      simpa only [deletionGraphHom, MonoidHom.prod_apply, MonoidHom.comp_apply,
        MonoidHom.inl_apply] using congrArg Prod.snd hw
    have hkill : Split.killOn p w = 1 :=
      Row.basisHom_injective (hsnd.trans (map_one Row.basisHom).symm)
    exact Subgroup.mem_map.mpr ⟨w, MonoidHom.mem_ker.mpr hkill, hfst⟩
  · rintro x ⟨w, hw, rfl⟩
    apply Subgroup.mem_comap.mpr
    refine MonoidHom.mem_range.mpr ⟨w, ?_⟩
    simp only [deletionGraphHom, MonoidHom.prod_apply, MonoidHom.comp_apply,
      MonoidHom.inl_apply]
    rw [MonoidHom.mem_ker.mp hw, map_one]

/-- Generic deletion-graph criterion.  It is enough that the subgroups
generated by the retained and deleted row basis elements are benign. -/
theorem benignTF_map_ker_killOn_of_parts (p : ℤ → Prop) [DecidablePred p]
    (hkeep : BenignTF ((indexSub p).map Row.basisHom))
    (hdrop : BenignTF ((indexSub (fun i => ¬ p i)).map Row.basisHom)) :
    BenignTF ((MonoidHom.ker (Split.killOn p)).map Row.basisHom) := by
  have hdiag : BenignTF (((indexSub p).map Row.basisHom).map diagHom) :=
    BenignTF.mapEmb
      (IsPowerTorsionFree.prod IsPowerTorsionFree.of_isMulTorsionFree
        IsPowerTorsionFree.of_isMulTorsionFree)
      hkeep diagHom diagHom_injective
  have hinl : BenignTF
      (((indexSub (fun i => ¬ p i)).map Row.basisHom).map
        (MonoidHom.inl F₀ F₀)) :=
    BenignTF.mapEmb
      (IsPowerTorsionFree.prod IsPowerTorsionFree.of_isMulTorsionFree
        IsPowerTorsionFree.of_isMulTorsionFree)
      hdrop (MonoidHom.inl F₀ F₀) (by
        intro x y h
        exact congrArg Prod.fst h)
  have hgraph : BenignTF (deletionGraphHom p).range := by
    rw [range_deletionGraphHom, map_indexSub_deletionGraph_keep,
      map_indexSub_deletionGraph_drop]
    exact BenignTF.sup hdiag hinl
  have hcomap := BenignTF.comap Row.f0Overgroup (MonoidHom.inl F₀ F₀) hgraph
  rwa [comap_range_deletionGraphHom] at hcomap

/-! ## Deletion at zero -/

/-- Reflection of the row carrier, `b ↦ b`, `c ↦ c⁻¹`. -/
def reflectHom : F₀ →* F₀ :=
  FreeGroup.lift fun i : Fin 2 => if i = 0 then Row.b else Row.c⁻¹

@[simp] theorem reflectHom_b : reflectHom Row.b = Row.b := by
  simp [reflectHom, Row.b]

@[simp] theorem reflectHom_c : reflectHom Row.c = Row.c⁻¹ := by
  simp [reflectHom, Row.c]

theorem reflectHom_comp_self : reflectHom.comp reflectHom = MonoidHom.id F₀ := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  rcases Row.fin_two_cases i with rfl | rfl
  · change reflectHom (reflectHom Row.b) = Row.b
    rw [reflectHom_b, reflectHom_b]
  · change reflectHom (reflectHom Row.c) = Row.c
    rw [reflectHom_c, map_inv, reflectHom_c, inv_inv]

/-- Reflection as an involutive automorphism. -/
def reflectEquiv : F₀ ≃* F₀ where
  toFun := reflectHom
  invFun := reflectHom
  left_inv x := congrArg (fun f : F₀ →* F₀ => f x) reflectHom_comp_self
  right_inv x := congrArg (fun f : F₀ →* F₀ => f x) reflectHom_comp_self
  map_mul' := map_mul reflectHom

@[simp] theorem reflectEquiv_apply (x : F₀) : reflectEquiv x = reflectHom x := rfl

theorem reflectHom_row (i : ℤ) : reflectHom (Row.row i) = Row.row (-i) := by
  unfold Row.row
  rw [map_mul, map_mul, map_zpow, map_zpow, reflectHom_b, reflectHom_c]
  have hleft : (Row.c⁻¹) ^ (-i) = Row.c ^ i := by
    calc
      (Row.c⁻¹) ^ (-i) = (Row.c ^ (-i))⁻¹ := inv_zpow Row.c (-i)
      _ = Row.c ^ i := by rw [← zpow_neg, neg_neg]
  have hright : (Row.c⁻¹) ^ i = Row.c ^ (-i) := by
    calc
      (Row.c⁻¹) ^ i = (Row.c ^ i)⁻¹ := inv_zpow Row.c i
      _ = Row.c ^ (-i) := by rw [← zpow_neg]
  rw [hleft, hright, neg_neg]

theorem map_indexSub_pos :
    (indexSub (fun i : ℤ => 0 < i)).map Row.basisHom = Row.PosHalfRow := by
  unfold indexSub Row.PosHalfRow
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, (Row.basisHom_of i).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨FreeGroup.of i, ⟨i, hi, rfl⟩, Row.basisHom_of i⟩

theorem map_indexSub_neg_reflect :
    ((indexSub (fun i : ℤ => i < 0)).map Row.basisHom).map reflectHom =
      Row.PosHalfRow := by
  rw [Subgroup.map_map]
  unfold indexSub Row.PosHalfRow
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    change i < 0 at hi
    refine ⟨-i, ?_, ?_⟩
    · change 0 < -i
      omega
    rw [MonoidHom.comp_apply, Row.basisHom_of, reflectHom_row]
  · rintro ⟨i, hi, rfl⟩
    change 0 < i at hi
    refine ⟨FreeGroup.of (-i), ⟨-i, ?_, rfl⟩, ?_⟩
    · change -i < 0
      omega
    rw [MonoidHom.comp_apply, Row.basisHom_of, reflectHom_row, neg_neg]

theorem benignTF_map_indexSub_neg :
    BenignTF ((indexSub (fun i : ℤ => i < 0)).map Row.basisHom) := by
  have h := BenignTF.congr reflectEquiv Row.benignTF_posHalfRow
  have himage :
      ((indexSub (fun i : ℤ => i < 0)).map Row.basisHom).map reflectHom =
        Row.PosHalfRow := map_indexSub_neg_reflect
  have hpre : Row.PosHalfRow.comap reflectHom =
      (indexSub (fun i : ℤ => i < 0)).map Row.basisHom := by
    rw [← himage]
    exact (Subgroup.comap_map_eq_self_of_injective reflectEquiv.injective) _
  change BenignTF (Row.PosHalfRow.comap reflectHom) at h
  rwa [hpre] at h

theorem indexSub_ne_zero :
    indexSub (fun i : ℤ => i ≠ 0) =
      indexSub (fun i : ℤ => i < 0) ⊔ indexSub (fun i : ℤ => 0 < i) := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, hi, rfl⟩
    change i ≠ 0 at hi
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨i, hneg, rfl⟩)
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨i, hpos, rfl⟩)
  · refine sup_le ?_ ?_
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨i, hi, rfl⟩
      change i < 0 at hi
      apply Subgroup.subset_closure
      refine ⟨i, ?_, rfl⟩
      change i ≠ 0
      omega
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨i, hi, rfl⟩
      change 0 < i at hi
      apply Subgroup.subset_closure
      refine ⟨i, ?_, rfl⟩
      change i ≠ 0
      omega

theorem benignTF_map_indexSub_ne_zero :
    BenignTF ((indexSub (fun i : ℤ => i ≠ 0)).map Row.basisHom) := by
  rw [indexSub_ne_zero, Subgroup.map_sup, map_indexSub_pos]
  exact BenignTF.sup benignTF_map_indexSub_neg Row.benignTF_posHalfRow

theorem benignTF_map_indexSub_eq_zero :
    BenignTF ((indexSub (fun i : ℤ => ¬ i ≠ 0)).map Row.basisHom) := by
  apply benignTF_of_fg IsPowerTorsionFree.of_isMulTorsionFree
  apply fg_map
  refine (Subgroup.fg_iff _).mpr
    ⟨FreeGroup.of '' {i : ℤ | ¬ i ≠ 0}, rfl, ?_⟩
  have hset : {i : ℤ | ¬ i ≠ 0} = {(0 : ℤ)} := by ext i; simp
  rw [hset]
  exact (Set.finite_singleton (0 : ℤ)).image FreeGroup.of

/-- The mapped normal closure of the zero-th row basis element is benign. -/
theorem benignTF_map_zetaV : BenignTF (Agree.zetaV.map Row.basisHom) := by
  exact benignTF_map_ker_killOn_of_parts (fun i : ℤ => i ≠ 0)
    benignTF_map_indexSub_ne_zero benignTF_map_indexSub_eq_zero

/-- **The `ζ` row leaf, discharged.** -/
theorem zeta_row_benignTF : BenignTF (Agree.rowSub Agree.zetaV) :=
  GroupApproximation.Higman.benignTF_rowSub_zetaV benignTF_map_zetaV

/-! ## Parity deletion -/

/-- Indices in the residue class `l` modulo two. -/
def residueSub (l : ℤ) : Subgroup (FreeGroup ℤ) :=
  indexSub (fun i => ∃ k : ℤ, i = 2 * k + l)

theorem map_residueSub_basisHom (l : ℤ) :
    (residueSub l).map Row.basisHom = Row.Row.map (Row.xi l) := by
  unfold residueSub indexSub Row.Row
  rw [MonoidHom.map_closure, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨i, ⟨k, rfl⟩, rfl⟩, rfl⟩
    exact ⟨Row.row k, ⟨k, rfl⟩, by rw [Row.xi_row, Row.basisHom_of]⟩
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨FreeGroup.of (2 * k + l), ?_, ?_⟩
    · exact ⟨2 * k + l, ⟨k, rfl⟩, rfl⟩
    rw [Row.basisHom_of, Row.xi_row]

theorem benignTF_Row : BenignTF Row.Row := by
  rw [Row.Row_eq_ker]
  exact ⟨TorsionFreeBenignWitness.ker
    IsPowerTorsionFree.of_isMulTorsionFree
    IsPowerTorsionFree.of_isMulTorsionFree Row.expHom⟩

theorem benignTF_map_residueSub (l : ℤ) :
    BenignTF ((residueSub l).map Row.basisHom) := by
  rw [map_residueSub_basisHom]
  exact BenignTF.mapEmb IsPowerTorsionFree.of_isMulTorsionFree benignTF_Row
    (Row.xi l) (Row.xi_injective l)

theorem indexSub_evenIdx : indexSub Seq.evenIdx = residueSub 0 := by
  congr 1
  funext i
  apply propext
  simpa [residueSub] using Seq.evenIdx_iff i

theorem not_evenIdx_iff (i : ℤ) : ¬ Seq.evenIdx i ↔ ∃ k : ℤ, i = 2 * k + 1 := by
  unfold Seq.evenIdx
  constructor
  · intro hi
    have hmod : i % 2 = 1 := by
      rcases Int.emod_two_eq i with hzero | hone
      · exact (hi hzero).elim
      · exact hone
    refine ⟨i / 2, ?_⟩
    have hdiv := Int.mul_ediv_add_emod i 2
    omega
  · rintro ⟨k, rfl⟩
    simp [Int.add_emod]

theorem indexSub_not_evenIdx :
    indexSub (fun i => ¬ Seq.evenIdx i) = residueSub 1 := by
  congr 1
  funext i
  exact propext (not_evenIdx_iff i)

/-- The mapped parity-deletion kernel is benign. -/
theorem benignTF_map_ker_killOn_evenIdx :
    BenignTF ((MonoidHom.ker (Split.killOn Seq.evenIdx)).map Row.basisHom) := by
  apply benignTF_map_ker_killOn_of_parts Seq.evenIdx
  · rw [indexSub_evenIdx]
    exact benignTF_map_residueSub 0
  · rw [indexSub_not_evenIdx]
    exact benignTF_map_residueSub 1

/-- **The even-deletion row leaf, discharged.** -/
theorem evenDeletion_row_benignTF :
    BenignTF (Agree.rowSub (MonoidHom.ker (Split.killOn Seq.evenIdx))) :=
  GroupApproximation.Higman.benignTF_rowSub_ker_killOn_evenIdx
    benignTF_map_ker_killOn_evenIdx

end RowDeletionGraph

end

end Higman
end GroupApproximation
