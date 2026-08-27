import GroupApproximation.Higman.OmegaTower
import GroupApproximation.Higman.CentralHNNFreeLabelKernel
import GroupApproximation.Higman.SwapCarrierWitness

/-!
# The two-sided Omega tower relation cannot satisfy descent

The decreasing-row counterexample uses the two structural tower relations
together with the former demand that selected codes centralize rows on both
sides of the active block.  It proves that this two-sided strengthening of the
corrected, order-sensitive `Tower` interface is incompatible with descent.
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
  · subst i
    exact (hi ⟨by omega, by omega⟩).elim
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
    have hi' : i = -1 := single_support_eq hi
    have hj' : j = 0 := single_support_eq hj
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

def TwoSidedRowsCommute (T : Tower 1) : Prop :=
  ∀ β ∈ blockSet 1, ∀ i : ℤ, i ∉ Finset.Ico (0 : ℤ) (1 : ℤ) →
    Commute (T.gen β) (T.emb (rowElt i))

noncomputable def towerCounterZ (T : Tower 1) : T.G :=
  (T.gen counterBeta)⁻¹ * T.emb (aElt counterLeft) * T.gen counterBeta

theorem towerCounterZ_eq (T : Tower 1) (htwo : TwoSidedRowsCommute T) :
    towerCounterZ T = T.emb counterX := by
  have hcomm : Commute (T.gen counterBeta) (T.emb (bElt counterLeft)) :=
    bElt_counterLeft ▸ htwo counterBeta counterBeta_mem_blockSet (-1) (by
      simp only [Finset.mem_Ico]
      omega)
  calc
    towerCounterZ T =
        (T.gen counterBeta)⁻¹ *
          ((T.emb (bElt counterLeft))⁻¹ * T.emb a *
            T.emb (bElt counterLeft)) * T.gen counterBeta := by
      rw [towerCounterZ, ← emb_aElt_eq]
    _ = (T.emb (bElt counterLeft))⁻¹ *
          ((T.gen counterBeta)⁻¹ * T.emb a * T.gen counterBeta) *
            T.emb (bElt counterLeft) := (conj_swap hcomm).symm
    _ = (T.emb (bElt counterLeft))⁻¹ *
          T.emb (aElt counterBeta) * T.emb (bElt counterLeft) := by
      rw [T.conj_gen counterBeta counterBeta_mem_blockSet]
    _ = T.emb counterX := by
      rw [emb_aElt_eq]
      unfold counterX counterQ
      simp only [map_mul, map_inv]
      group

theorem towerCounterZ_mem_W (T : Tower 1) :
    towerCounterZ T ∈ W T (blockSet 1) := by
  have hg : T.gen counterBeta ∈ W T (blockSet 1) :=
    gen_mem_W T counterBeta_mem_blockSet counterBeta_mem_blockSet
  have ha : T.emb (aElt counterLeft) ∈ W T (blockSet 1) := by
    apply ASub_omegaOp_le (by omega) T (by
      intro i _
      rfl)
    exact Subgroup.subset_closure ⟨counterLeft, counterLeft_mem_omega, rfl⟩
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) ha) hg

/-- No tower with the extra two-sided row commutation can satisfy the
advertised descent for the maximal legal one-block alphabet. -/
theorem not_tower_descent_one_blockSet (T : Tower 1)
    (htwo : TwoSidedRowsCommute T) :
    ¬ (∀ x : F₃, T.emb x ∈ W T (blockSet 1) →
      x ∈ ASub (omegaOp 1 (blockSet 1))) := by
  intro h
  apply counterX_not_mem_ASub_univ
  rw [← omegaOp_one_blockSet_eq_univ]
  apply h counterX
  rw [← towerCounterZ_eq T htwo]
  exact towerCounterZ_mem_W T

/-- **Interface-level no-go.**  Adding the former two-sided commutation rule
rules out a closure witness already at block width one. -/
theorem not_towerClosure_of_twoSidedRowsCommute (T : Tower 1)
    (htwo : TwoSidedRowsCommute T) :
    ¬ TowerClosure T (blockSet 1) := by
  intro h
  exact not_tower_descent_one_blockSet T htwo h.descent

end Omega
end Higman
end GroupApproximation
