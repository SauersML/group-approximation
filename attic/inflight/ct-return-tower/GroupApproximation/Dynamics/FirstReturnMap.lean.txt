import GroupApproximation.Dynamics.ReturnSection

/-!
# First return to a return section

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`
(`\label{cor:dynamic-rank-budget}`), tex 1721–1722:

> Let $C_h$ be the clopen first-return-time cells and $S_C$ the
> first-return homeomorphism.

For a return section `C` of `T` (`IsReturnSection T r C`):

* `returnCell T C h = {x ∈ C | returnTime T C x = h}`, `returnCell_eq` (it is
  `C ∩ T^{-h} C ∩ ⋂_{0<j<h} T^{-j} Cᶜ`), `isClopen_returnCell`;
* `IsReturnSection.inv`: `C` is also a return section of `T⁻¹`;
* `firstReturnFun hC : C → C`, `x ↦ T^{h(x)} x`, continuous because it is `T^h` on each clopen
  cell; its inverse is the first-return map of `T⁻¹`;
* `firstReturnHomeomorph hC : C ≃ₜ C`, the printed `S_C`;
* the closed endpoint `firstReturnStatement_holds : FirstReturnStatement`.
-/

namespace GroupApproximation.ChainCore

open Set Topology

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X} {r : ℕ} {C : Set X}

/-- The first-return-time cell `C_h`. -/
def returnCell (T : X ≃ₜ X) (C : Set X) (h : ℕ) : Set X :=
  {x | x ∈ C ∧ returnTime T C x = h}

theorem returnCell_eq (hC : IsReturnSection T r C) {h : ℕ} (hh : 0 < h) :
    returnCell T C h =
      C ∩ (T ^ (h : ℤ)) ⁻¹' C ∩ ⋂ j ∈ Finset.Ioo 0 h, (T ^ (j : ℤ)) ⁻¹' Cᶜ := by
  ext x
  simp only [returnCell, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_iInter₂, Finset.mem_Ioo,
    mem_compl_iff]
  constructor
  · rintro ⟨hx, rfl⟩
    exact ⟨⟨hx, (returnTime_spec hC x).2⟩, fun j hj => returnTime_min hC x hj.1 hj.2⟩
  · rintro ⟨⟨hx, hhC⟩, hmin⟩
    exact ⟨hx, returnTime_eq_of hC x hh hhC fun j h₁ h₂ => hmin j ⟨h₁, h₂⟩⟩

theorem returnCell_zero (hC : IsReturnSection T r C) : returnCell T C 0 = ∅ :=
  eq_empty_of_forall_notMem fun x hx => (returnTime_spec hC x).1.ne' hx.2

/-- **The first-return-time cells are clopen** (tex 1721). -/
theorem isClopen_returnCell (hC : IsReturnSection T r C) (h : ℕ) :
    IsClopen (returnCell T C h) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · rw [returnCell_zero hC]
    exact isClopen_empty
  · rw [returnCell_eq hC hh]
    exact (hC.isClopen.inter (hC.isClopen.preimage (T ^ (h : ℤ)).continuous)).inter
      (isClopen_biInter_finset fun j _ => hC.isClopen.compl.preimage (T ^ (j : ℤ)).continuous)

theorem mem_returnCell_returnTime {x : X} (hx : x ∈ C) : x ∈ returnCell T C (returnTime T C x) :=
  ⟨hx, rfl⟩

/-- `C` is a return section of `T⁻¹` as well. -/
theorem IsReturnSection.inv (hC : IsReturnSection T r C) : IsReturnSection T⁻¹ r C where
  isClopen := hC.isClopen
  disjoint_image j h₁ h₂ := by
    refine disjoint_left.2 fun y hy hyimg => ?_
    obtain ⟨z, hz, rfl⟩ := hyimg
    refine disjoint_left.1 (hC.disjoint_image j h₁ h₂) hz ⟨(T⁻¹ ^ (j : ℤ)) z, hy, ?_⟩
    rw [inv_zpow', zpow_apply_zpow_apply_homeomorph, add_neg_cancel, zpow_zero,
      Homeomorph.one_apply]
  exists_mem_image x := by
    obtain ⟨j, hj, c, hc, hcx⟩ := hC.exists_mem_image x
    refine ⟨-j, by rwa [abs_neg], c, hc, ?_⟩
    rw [inv_zpow', neg_neg]
    exact hcx

/-- The first return of `T⁻¹` to `T^{h(x)} x` takes `h(x)` steps. -/
theorem returnTime_inv_zpow_returnTime (hC : IsReturnSection T r C) {x : X} (hx : x ∈ C) :
    returnTime T⁻¹ C ((T ^ (returnTime T C x : ℤ)) x) = returnTime T C x := by
  obtain ⟨h₁, h₃⟩ := returnTime_spec hC x
  refine returnTime_eq_of hC.inv _ h₁ ?_ ?_
  · rw [inv_zpow', zpow_neg_apply_zpow_apply_homeomorph]
    exact hx
  · intro j hj₁ hj₂ hjC
    refine returnTime_min hC x (j := returnTime T C x - j) (by omega) (by omega) ?_
    rw [inv_zpow', zpow_apply_zpow_apply_homeomorph] at hjC
    rwa [show ((returnTime T C x - j : ℕ) : ℤ) = -(j : ℤ) + (returnTime T C x : ℤ) by
      rw [Nat.cast_sub hj₂.le]
      ring]

theorem zpow_inv_returnTime_zpow_returnTime (hC : IsReturnSection T r C) {x : X} (hx : x ∈ C) :
    (T⁻¹ ^ (returnTime T⁻¹ C ((T ^ (returnTime T C x : ℤ)) x) : ℤ))
        ((T ^ (returnTime T C x : ℤ)) x) = x := by
  rw [returnTime_inv_zpow_returnTime hC hx, inv_zpow', zpow_neg_apply_zpow_apply_homeomorph]

/-- The first-return map `x ↦ T^{h(x)} x` of `C`. -/
noncomputable def firstReturnFun (hC : IsReturnSection T r C) (x : C) : C :=
  ⟨(T ^ (returnTime T C x : ℤ)) x, (returnTime_spec hC x).2⟩

theorem coe_firstReturnFun (hC : IsReturnSection T r C) (x : C) :
    (firstReturnFun hC x : X) = (T ^ (returnTime T C x : ℤ)) x :=
  rfl

theorem continuous_firstReturnFun (hC : IsReturnSection T r C) :
    Continuous (firstReturnFun hC) := by
  show Continuous fun x : C =>
    (⟨(T ^ (returnTime T C x : ℤ)) x, (returnTime_spec hC x).2⟩ : C)
  refine Continuous.subtype_mk (continuous_iff_continuousAt.2 fun x => ?_) _
  have hU : IsOpen {y : C | returnTime T C y = returnTime T C x} := by
    have hpre : {y : C | returnTime T C y = returnTime T C x} =
        Subtype.val ⁻¹' returnCell T C (returnTime T C x) := by
      ext y
      simp only [mem_setOf_eq, mem_preimage, returnCell, y.2, true_and]
    rw [hpre]
    exact (isClopen_returnCell hC _).isOpen.preimage continuous_subtype_val
  refine ((T ^ (returnTime T C x : ℤ)).continuous.comp continuous_subtype_val).continuousAt.congr ?_
  refine Filter.eventuallyEq_of_mem (hU.mem_nhds (show x ∈ {y : C | _} from rfl)) fun y hy => ?_
  simp only [Function.comp_apply, mem_setOf_eq] at hy ⊢
  rw [hy]

theorem firstReturnFun_inv_firstReturnFun (hC : IsReturnSection T r C) (x : C) :
    firstReturnFun hC.inv (firstReturnFun hC x) = x :=
  Subtype.ext (zpow_inv_returnTime_zpow_returnTime hC x.2)

theorem firstReturnFun_firstReturnFun_inv (hC : IsReturnSection T r C) (x : C) :
    firstReturnFun hC (firstReturnFun hC.inv x) = x := by
  apply Subtype.ext
  have h := zpow_inv_returnTime_zpow_returnTime hC.inv x.2
  rw [inv_inv] at h
  exact h

/-- **The first-return homeomorphism `S_C`** (tex 1722). -/
noncomputable def firstReturnHomeomorph (hC : IsReturnSection T r C) : C ≃ₜ C where
  toFun := firstReturnFun hC
  invFun := firstReturnFun hC.inv
  left_inv := firstReturnFun_inv_firstReturnFun hC
  right_inv := firstReturnFun_firstReturnFun_inv hC
  continuous_toFun := continuous_firstReturnFun hC
  continuous_invFun := continuous_firstReturnFun hC.inv

theorem firstReturnHomeomorph_apply (hC : IsReturnSection T r C) (x : C) :
    (firstReturnHomeomorph hC x : X) = (T ^ (returnTime T C x : ℤ)) x :=
  rfl

theorem firstReturnHomeomorph_symm_apply (hC : IsReturnSection T r C) (x : C) :
    ((firstReturnHomeomorph hC).symm x : X) = (T⁻¹ ^ (returnTime T⁻¹ C x : ℤ)) x :=
  rfl

/-- **First return** (tex 1721–1722), closed: return times in `[r, 2r - 1]`, clopen cells, and
the first-return homeomorphism. -/
theorem firstReturnStatement_holds : FirstReturnStatement := by
  intro X _ T r C _ hC
  exact ⟨fun x hx => ⟨le_returnTime hC hx, returnTime_le hC x, (returnTime_spec hC x).2⟩,
    fun h => isClopen_returnCell hC h, firstReturnHomeomorph hC, fun _ => rfl⟩

end GroupApproximation.ChainCore

open GroupApproximation.ChainCore

#audit_closed_axioms firstReturnStatement_holds
#audit_axioms firstReturnHomeomorph
