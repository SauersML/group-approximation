import GroupApproximation.Higman.OmegaTowerStaticSeamCoordinates
import GroupApproximation.Higman.SwapCarrierWitness

/-!
# Counterexample to the proposed static Omega seam

With free (rather than commuting) row letters, a selected code can move a
legal conjugator supported one block to the left past the active block.  The
resulting conjugator has the two row letters in decreasing order, so it is not
the canonical code of any sequence.  Thus the proposed stable-hull bound is
false for the current slim tower.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

noncomputable def counterBeta : E := Finsupp.single (0 : ℤ) 1
noncomputable def counterLeft : E := Finsupp.single (-1 : ℤ) 1

theorem counterBeta_mem_blockSet : counterBeta ∈ blockSet 1 := by
  intro i hi
  rw [counterBeta, Finsupp.single_apply]
  simp only [Finset.mem_Ico] at hi
  split_ifs with h
  · subst i; exact (hi ⟨by omega, by omega⟩).elim
  · rfl

theorem counterLeft_mem_omega : counterLeft ∈ omegaOp 1 (blockSet 1) := by
  intro i
  exact blockAt_mem_blockSet 1 i counterLeft

theorem rowElt_negOne_zero_not_commute :
    rowElt (-1) * rowElt 0 ≠ rowElt 0 * rowElt (-1) := by
  intro h
  have hs := congrArg shiftAut h
  simp only [map_mul, shiftAut_rowElt] at hs
  norm_num at hs
  exact rowElt_zero_one_not_commute hs

theorem bElt_counterBeta : bElt counterBeta = rowElt 0 := by
  rw [counterBeta, bElt_single, zpow_one]

theorem bElt_counterLeft : bElt counterLeft = rowElt (-1) := by
  rw [counterLeft, bElt_single, zpow_one]

noncomputable def counterQ : ↥K :=
  ⟨bElt counterBeta * bElt counterLeft,
    K.mul_mem (bElt_mem_K counterBeta) (bElt_mem_K counterLeft)⟩

/-- The decreasing two-row word is not the canonical code of any sequence. -/
theorem counter_conjugator_not_mem_bK_range :
    counterQ ∉ Set.range bK := by
  rintro ⟨f, hf⟩
  have hb : bElt f = bElt counterBeta * bElt counterLeft :=
    congrArg Subtype.val hf
  have he : elt f = elt counterBeta * elt counterLeft := by
    apply rowHom_injective
    simpa only [bElt, map_mul] using hb
  have hab := congrArg ab he
  have hfseq : f = counterBeta + counterLeft := by
    simp only [ab_elt, map_mul] at hab
    change f = counterBeta + counterLeft at hab
    exact hab
  have hcanon :
      bElt (counterBeta + counterLeft) =
        bElt counterLeft * bElt counterBeta := by
    rw [add_comm]
    apply bElt_add_of_lt
    intro i hi j hj
    have hi' : i = -1 := by
      exact single_support_eq hi
    have hj' : j = 0 := by
      exact single_support_eq hj
    omega
  rw [hfseq, hcanon, bElt_counterBeta, bElt_counterLeft] at hb
  exact rowElt_negOne_zero_not_commute hb

noncomputable def counterX : F₃ :=
  (counterQ : F₃)⁻¹ * a * (counterQ : F₃)

theorem counterX_not_mem_ASub_univ : counterX ∉ ASub (Set.univ : Set E) := by
  intro hx
  rw [ASub_eq_map] at hx
  obtain ⟨w, hw, hwx⟩ := hx
  have hcb : Conj.cbHom (FreeGroup.of counterQ) = counterX := by
    simp only [Conj.cbHom_of]
    rfl
  have hwq : w = FreeGroup.of counterQ :=
    Conj.cbHom_injective (hwx.trans hcb.symm)
  rw [hwq] at hw
  have hindex := CentralHNNFreeLabel.Coordinate.index_mem_of_of_mem_closure hw
  apply counter_conjugator_not_mem_bK_range
  obtain ⟨f, -, hf⟩ := hindex
  exact ⟨f, hf⟩

theorem omegaOp_one_blockSet_eq_univ :
    omegaOp 1 (blockSet 1) = (Set.univ : Set E) := by
  ext f
  simp only [Set.mem_univ, iff_true]
  exact fun i => blockAt_mem_blockSet 1 i f

noncomputable def counterG : SlimPi 1 :=
  slimPiOf 1 (slimGenCode 1 counterBeta)

noncomputable def counterZ : SlimPi 1 :=
  counterG⁻¹ * slimPiF3Hom 1 (aElt counterLeft) * counterG

theorem counterZ_eq : counterZ = slimPiF3Hom 1 counterX := by
  have h := slimGen_conj_aElt_eq_rowConj_of_outside
    (m := 1) (β := counterBeta) (l := counterLeft)
    counterBeta_mem_blockSet (by
      intro i hi
      rw [counterLeft, Finsupp.single_apply] at hi
      split_ifs at hi with hidx
      · subst i
        simp only [Finset.mem_Ico]
        omega
      · exact (hi rfl).elim)
  rw [counterZ, counterG, h]
  unfold counterX counterQ aElt
  simp only [map_mul, map_inv]
  group

theorem counterZ_mem_staticSeam_source :
    counterZ ∈
      (slimWBase 1 (blockSet 1) ⊔ omegaRangeSub 1 (blockSet 1)) ⊓
        (slimPiF3Hom 1).range := by
  constructor
  · have hg : counterG ∈ slimWBase 1 (blockSet 1) := by
      apply Subgroup.subset_closure
      exact Set.mem_union_right _
        ⟨counterBeta, ⟨counterBeta_mem_blockSet, counterBeta_mem_blockSet⟩, rfl⟩
    have ha : slimPiF3Hom 1 (aElt counterLeft) ∈
        omegaRangeSub 1 (blockSet 1) := by
      refine ⟨aElt counterLeft, ?_, rfl⟩
      apply Subgroup.subset_closure
      exact ⟨counterLeft, counterLeft_mem_omega, rfl⟩
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hg))
        (Subgroup.mem_sup_right ha))
      (Subgroup.mem_sup_left hg)
  · exact ⟨counterX, counterZ_eq.symm⟩

theorem counterZ_not_mem_omegaRangeSub :
    counterZ ∉ omegaRangeSub 1 (blockSet 1) := by
  intro hz
  obtain ⟨x, hx, hzx⟩ := hz
  have hxx : x = counterX :=
    slimPiF3Hom_injective 1 (hzx.trans counterZ_eq)
  rw [hxx, omegaOp_one_blockSet_eq_univ] at hx
  exact counterX_not_mem_ASub_univ hx

/-- **The current static seam is false.** -/
theorem not_staticSeam_one_blockSet : ¬ StaticSeam 1 (blockSet 1) := by
  intro h
  exact counterZ_not_mem_omegaRangeSub (h counterZ_mem_staticSeam_source)

/-- **Counterexample to the original Omega descent target.**  This is not
merely a failure of the auxiliary static seam: the same conjugate belongs to
the exact outer stable hull, hence to the original subgroup `W`, but its
preimage is outside the prescribed arithmetic subgroup. -/
theorem exists_mem_slimW_not_mem_ASub_omega :
    ∃ x : F₃,
      slimOmegaEmb 1 x ∈ W (slimTower 1) (blockSet 1) ∧
        x ∉ ASub (omegaOp 1 (blockSet 1)) := by
  refine ⟨counterX, ?_, ?_⟩
  · apply slimPiF3Hom_mem_outerStableHull_iff.mp
    rw [← counterZ_eq]
    apply (sup_le
      (HNNDescent.le_stableHull
        (slimShiftRangeEquiv 1) (slimWBase 1 (blockSet 1)))
      (omegaRangeSub_le_outerStableHull (m := 1) (B := blockSet 1)
        (by omega) (by
          intro i
          simp)))
    exact counterZ_mem_staticSeam_source.1
  · rw [omegaOp_one_blockSet_eq_univ]
    exact counterX_not_mem_ASub_univ

/-- In particular, the current slim tower cannot supply its advertised
descent field, even for the first block size and the maximal legal block
alphabet. -/
theorem not_slimTower_descent_one_blockSet :
    ¬ (∀ x : F₃,
      slimOmegaEmb 1 x ∈ W (slimTower 1) (blockSet 1) →
        x ∈ ASub (omegaOp 1 (blockSet 1))) := by
  rintro h
  obtain ⟨x, hxW, hxA⟩ := exists_mem_slimW_not_mem_ASub_omega
  exact hxA (h x hxW)

/-- The concrete slim tower therefore cannot discharge `TowerClosure`.  This
does not refute the abstract `OmegaInput`: it isolates the failure of this
particular modified Mikaelian tower. -/
theorem not_towerClosure_slimTower_one_blockSet :
    ¬ TowerClosure (slimTower 1) (blockSet 1) := by
  intro h
  exact not_slimTower_descent_one_blockSet h.descent

end Omega
end Higman
end GroupApproximation
