import GroupApproximation.Higman.CentralHNNFreeLabelRightAction
import GroupApproximation.Higman.OmegaTowerRightTailCollapse
import GroupApproximation.Higman.OmegaTowerStaticSeamFreeCoordinates

/-!
# Exact right action on Omega row labels

The generic right action on central-HNN labels specializes to block
prepending.  Its image is again a row label exactly when the old sequence is
supported to the right of the active block.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq
open HNNExtension

noncomputable def slimRightLabel (m : ℕ) (β : E)
    (q : CentralHNNFreeLabel.Label (slimLink m) (slimTransversal m)) :
    CentralHNNFreeLabel.Label (slimLink m) (slimTransversal m) :=
  CentralHNNFreeLabel.rightLabel (M := slimLink m) (slimTransversal m)
    (slimGenCode m β) q

theorem slimRightLabel_injective (m : ℕ) (β : E) :
    Function.Injective (slimRightLabel m β) :=
  CentralHNNFreeLabel.rightLabel_injective
    (M := slimLink m) (slimTransversal m) (slimGenCode m β)

/-- On a right-tail sequence, label translation is literally canonical block
prepending. -/
theorem slimRightLabel_rowLabel_eq {m : ℕ} {β l : E}
    (hβ : β ∈ blockSet m)
    (hl : ∀ i : ℤ, l i ≠ 0 → (m : ℤ) ≤ i) :
    slimRightLabel m β (slimRowLabel m (bK l)) =
      slimRowLabel m (bK (β + l)) := by
  have hright := CentralHNNFreeLabel.stableConj_rightLabel
    (M := slimLink m) (slimTransversal m) (slimGenCode m β)
      (slimRowLabel m (bK l))
  have hcollapse := slimGen_conj_aElt_eq_aElt_add_rightTail hβ hl
  rw [slimPiF3Hom_aElt_eq_stableConj_rowLabel,
    slimPiF3Hom_aElt_eq_stableConj_rowLabel] at hcollapse
  have heq :
      CentralHNNFreeLabel.stableConj (slimLink m) (slimTransversal m)
          (slimRightLabel m β (slimRowLabel m (bK l))) =
        CentralHNNFreeLabel.stableConj (slimLink m) (slimTransversal m)
          (slimRowLabel m (bK (β + l))) := by
    exact hright.symm.trans hcollapse
  have haction := congrArg
    (fun z => CentralHNNFreeLabel.action (slimLink m) (slimTransversal m) z
      ((1 : Cent3 (rowOut m)),
        (1 : FreeGroup (CentralHNNFreeLabel.Label
          (slimLink m) (slimTransversal m))))) heq
  rw [CentralHNNFreeLabel.action_stableConj_apply_one,
    CentralHNNFreeLabel.action_stableConj_apply_one] at haction
  exact FreeGroup.of_injective (congrArg Prod.snd haction)

/-- Exact order test on a translated canonical row label.  Translation lands
back in the row-label alphabet precisely for right-tail sequences. -/
theorem slimRightLabel_rowLabel_mem_range_iff
    {m : ℕ} {β l : E} (hβ : β ∈ blockSet m) :
    slimRightLabel m β (slimRowLabel m (bK l)) ∈
        Set.range (slimRowLabel m) ↔
      ∀ i : ℤ, l i ≠ 0 → (m : ℤ) ≤ i := by
  constructor
  · rintro ⟨q, hq⟩
    apply (slimGen_conj_aElt_mem_F3Range_iff hβ).mp
    refine ⟨Conj.cbHom (FreeGroup.of q), ?_⟩
    have hright := CentralHNNFreeLabel.stableConj_rightLabel
      (M := slimLink m) (slimTransversal m) (slimGenCode m β)
        (slimRowLabel m (bK l))
    have hfree := DFunLike.congr_fun
      (slimPiF3Hom_comp_cbHom_eq_freeLabel m) (FreeGroup.of q)
    symm
    calc
      (slimPiOf m (slimGenCode m β))⁻¹ * slimPiF3Hom m (aElt l) *
          slimPiOf m (slimGenCode m β) =
          CentralHNNFreeLabel.stableConj (slimLink m) (slimTransversal m)
            (slimRightLabel m β (slimRowLabel m (bK l))) := by
              rw [slimPiF3Hom_aElt_eq_stableConj_rowLabel]
              exact hright
      _ = CentralHNNFreeLabel.stableConj (slimLink m) (slimTransversal m)
            (slimRowLabel m q) := by rw [hq]
      _ = slimPiF3Hom m (Conj.cbHom (FreeGroup.of q)) := by
            change CentralHNNFreeLabel.stableConj
              (slimLink m) (slimTransversal m) (slimLabelIndex m q) = _
            simpa only [MonoidHom.comp_apply, slimLabelHom_of,
              CentralHNNFreeLabel.stableConjLift,
              FreeGroup.lift_apply_of] using hfree.symm
  · intro hl
    exact ⟨bK (β + l), (slimRightLabel_rowLabel_eq hβ hl).symm⟩

/-- Word-level reflection: if translating a free label word creates only row
labels, then its original support lies in the exact preimage of the row-label
alphabet. -/
theorem mem_preimage_rowLabels_of_map_mem_rowLabels
    {m : ℕ} {β : E}
    {w : FreeGroup (CentralHNNFreeLabel.Label
      (slimLink m) (slimTransversal m))}
    (hw : FreeGroup.map (slimRightLabel m β) w ∈
      Subgroup.closure (FreeGroup.of '' Set.range (slimRowLabel m))) :
    w ∈ Subgroup.closure (FreeGroup.of ''
      {q | slimRightLabel m β q ∈ Set.range (slimRowLabel m)}) := by
  exact CentralHNNFreeLabel.Coordinate.mem_closure_preimage_of_map_mem
    (slimRightLabel_injective m β) (Set.range (slimRowLabel m)) hw

/-- **Multi-letter order theorem.**  A word supported on canonical Omega
labels whose selected-code translate returns to the row-label alphabet stays
inside the canonical Omega label subgroup.  Free-coordinate intersection
removes cancellations first; the exact one-letter seam then prepends the
selected block to every surviving basis index. -/
theorem map_slimRightLabel_mem_omegaLabelSub
    {m : ℕ} (hm : 0 < m) {B : Set E} {β : E}
    (hβ : β ∈ B ∩ blockSet m)
    {w : FreeGroup (CentralHNNFreeLabel.Label
      (slimLink m) (slimTransversal m))}
    (hwOmega : w ∈ omegaLabelSub m B)
    (hwRows : FreeGroup.map (slimRightLabel m β) w ∈
      Subgroup.closure (FreeGroup.of '' Set.range (slimRowLabel m))) :
    FreeGroup.map (slimRightLabel m β) w ∈ omegaLabelSub m B := by
  have hwPre := mem_preimage_rowLabels_of_map_mem_rowLabels hwRows
  have hwInter : w ∈ Subgroup.closure (FreeGroup.of ''
      (omegaLabelSet m B ∩
        {q | slimRightLabel m β q ∈ Set.range (slimRowLabel m)})) := by
    apply CentralHNNFreeLabel.Coordinate.closure_inter_le
      (omegaLabelSet m B)
      {q | slimRightLabel m β q ∈ Set.range (slimRowLabel m)}
    exact ⟨hwOmega, hwPre⟩
  refine Subgroup.closure_induction
    (p := fun w _ => FreeGroup.map (slimRightLabel m β) w ∈
      omegaLabelSub m B) ?_ ?_ ?_ ?_ hwInter
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨_k, ⟨l, hlOmega, rfl⟩, rfl⟩ := hq.1
    have hlTail :=
      (slimRightLabel_rowLabel_mem_range_iff hβ.2).mp hq.2
    rw [FreeGroup.map.of, slimRightLabel_rowLabel_eq hβ.2 hlTail]
    apply Subgroup.subset_closure
    exact ⟨slimRowLabel m (bK (β + l)),
      ⟨bK (β + l),
        ⟨β + l, add_rightTail_mem_omegaOp hm hβ hlTail hlOmega, rfl⟩,
        rfl⟩,
      rfl⟩
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro x y _ _ hx hy
    rw [map_mul]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    rw [map_inv]
    exact Subgroup.inv_mem _ hx

theorem exists_cbWord_of_slimPiF3Hom_baseRet_eq_one
    {m : ℕ} {x : F₃}
    (hx : slimPiBaseRet m (slimPiF3Hom m x) = 1) :
    ∃ w : FreeGroup ↥Conj.K, Conj.cbHom w = x := by
  have hret : Coord.retK x = 1 := by
    rw [← rowIntoF3_baseRet3_slimPiBaseRet_comp_slimPiF3Hom m,
      MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
      hx, map_one, map_one]
  have hker : x ∈ MonoidHom.ker Coord.retK := MonoidHom.mem_ker.mpr hret
  rw [ker_retK_eq_cbHom_range] at hker
  exact hker

/-- **Multi-letter Cases 2/3.**  Conjugating an arbitrary element of the
canonical Omega range by one selected code cannot return to the embedded
`F₃` anywhere outside the Omega range. -/
theorem slimGen_conj_omegaRange_mem_of_mem_F3Range
    {m : ℕ} (hm : 0 < m) {B : Set E} {β : E}
    (hβ : β ∈ B ∩ blockSet m) {z : SlimPi m}
    (hz : z ∈ omegaRangeSub m B)
    (hsurvives :
      (slimPiOf m (slimGenCode m β))⁻¹ * z *
          slimPiOf m (slimGenCode m β) ∈ (slimPiF3Hom m).range) :
    (slimPiOf m (slimGenCode m β))⁻¹ * z *
        slimPiOf m (slimGenCode m β) ∈ omegaRangeSub m B := by
  rw [omegaRangeSub_eq_map_omegaLabelSub] at hz
  obtain ⟨w, hwOmega, rfl⟩ := hz
  obtain ⟨x, hx⟩ := hsurvives
  have hbase : slimPiBaseRet m (slimPiF3Hom m x) = 1 := by
    rw [hx, slimPiBaseRet_eq_freeLabelBaseRet]
    change CentralHNNFreeLabel.baseRet (slimLink m)
      (of (slimGenCode m β)⁻¹ *
        CentralHNNFreeLabel.stableConjLift
          (slimLink m) (slimTransversal m) w *
        of (slimGenCode m β)) = 1
    have hwker : CentralHNNFreeLabel.baseRet (slimLink m)
        (CentralHNNFreeLabel.stableConjLift
          (slimLink m) (slimTransversal m) w) = 1 := by
      rw [← MonoidHom.comp_apply,
        CentralHNNFreeLabel.baseRet_comp_stableConjLift]
      rfl
    have hg : CentralHNNFreeLabel.baseRet (slimLink m)
        (of (slimGenCode m β)⁻¹) = (slimGenCode m β)⁻¹ := by
      simpa only [map_inv] using congrArg Inv.inv
        (CentralHNNFreeLabel.baseRet_of
          (M := slimLink m) (slimGenCode m β))
    rw [map_mul, map_mul, hg, hwker,
      CentralHNNFreeLabel.baseRet_of]
    group
  obtain ⟨v, hv⟩ := exists_cbWord_of_slimPiF3Hom_baseRet_eq_one hbase
  have hright := CentralHNNFreeLabel.stableConjLift_rightLabel
    (M := slimLink m) (slimTransversal m) (slimGenCode m β) w
  have hfree := DFunLike.congr_fun
    (slimPiF3Hom_comp_cbHom_eq_freeLabel m) v
  change slimPiF3Hom m (Conj.cbHom v) =
    CentralHNNFreeLabel.stableConjLift
      (slimLink m) (slimTransversal m) (slimLabelHom m v) at hfree
  have heval :
      CentralHNNFreeLabel.stableConjLift (slimLink m) (slimTransversal m)
          (FreeGroup.map (slimRightLabel m β) w) =
        CentralHNNFreeLabel.stableConjLift (slimLink m) (slimTransversal m)
          (slimLabelHom m v) := by
    change CentralHNNFreeLabel.stableConjLift
        (slimLink m) (slimTransversal m)
          (FreeGroup.map
            (CentralHNNFreeLabel.rightLabel (M := slimLink m)
              (slimTransversal m) (slimGenCode m β)) w) = _
    rw [← hright, ← hfree, hv, hx]
    simp only [slimPiOf, map_inv]
  have hword : FreeGroup.map (slimRightLabel m β) w = slimLabelHom m v :=
    CentralHNNFreeLabel.stableConjLift_injective
      (slimLink m) (slimTransversal m) heval
  have hvRows : slimLabelHom m v ∈
      Subgroup.closure (FreeGroup.of '' Set.range (slimRowLabel m)) := by
    have hv' := CentralHNNFreeLabel.Coordinate.map_mem_closure_range
      (slimLabelIndex m) v
    change slimLabelHom m v ∈
      Subgroup.closure (FreeGroup.of '' Set.range (slimLabelIndex m))
    exact hv'
  have hwRows : FreeGroup.map (slimRightLabel m β) w ∈
      Subgroup.closure (FreeGroup.of '' Set.range (slimRowLabel m)) := by
    rwa [hword]
  have hwOmega' :=
    map_slimRightLabel_mem_omegaLabelSub hm hβ hwOmega hwRows
  rw [omegaRangeSub_eq_map_omegaLabelSub]
  exact ⟨FreeGroup.map (slimRightLabel m β) w, hwOmega', hright.symm⟩

end Omega
end Higman
end GroupApproximation
