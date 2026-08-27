import GroupApproximation.Higman.OmegaTowerRightLabel
import GroupApproximation.Higman.CentralHNNFreeLabelAffine

/-!
# The inverse selected-letter rule on canonical Omega labels

If inverse translation by one selected code carries one canonical row label
to another, reversing the equality gives the already-classified positive
pinch.  Hence the source sequence begins with that selected block and the
target is its right tail.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq
open HNNExtension

/-- The positive selected-letter transition preserves the Omega language. -/
theorem omega_mem_of_rightLabel_rowLabel_eq
    {m : ℕ} (hm : 0 < m) {B : Set E}
    {β l f : E} (hβ : β ∈ B ∩ blockSet m) (hl : l ∈ omegaOp m B)
    (hlabel : slimRightLabel m β (slimRowLabel m (bK l)) =
      slimRowLabel m (bK f)) :
    f ∈ omegaOp m B := by
  have hlTail := (slimRightLabel_rowLabel_mem_range_iff hβ.2).mp
    ⟨bK f, hlabel.symm⟩
  have hadd := slimRightLabel_rowLabel_eq hβ.2 hlTail
  have hindex : bK f = bK (β + l) :=
    slimLabelIndex_injective m (hlabel.symm.trans hadd)
  have hseq : f = β + l := bK_injective hindex
  rw [hseq]
  exact add_rightTail_mem_omegaOp hm hβ hlTail hl

/-- Exact inverse one-letter transition between canonical row labels. -/
theorem rightLabel_inv_rowLabel_eq_iff
    {m : ℕ} {β l f : E} (hβ : β ∈ blockSet m) :
    CentralHNNFreeLabel.rightLabel
        (M := slimLink m) (slimTransversal m) (slimGenCode m β)⁻¹
          (slimRowLabel m (bK l)) = slimRowLabel m (bK f) ↔
      (∀ i : ℤ, f i ≠ 0 → (m : ℤ) ≤ i) ∧ l = β + f := by
  constructor
  · intro hlabel
    have hright := CentralHNNFreeLabel.stableConj_rightLabel
      (M := slimLink m) (slimTransversal m) (slimGenCode m β)⁻¹
        (slimRowLabel m (bK l))
    rw [hlabel] at hright
    have hright' :
        of (slimGenCode m β) *
              CentralHNNFreeLabel.stableConj
                (slimLink m) (slimTransversal m)
                  (slimRowLabel m (bK l)) *
            (of (slimGenCode m β))⁻¹ =
          CentralHNNFreeLabel.stableConj
            (slimLink m) (slimTransversal m)
              (slimRowLabel m (bK f)) := by
      simpa only [map_inv, inv_inv] using hright
    have hpositive :
        (slimPiOf m (slimGenCode m β))⁻¹ *
            slimPiF3Hom m (aElt f) * slimPiOf m (slimGenCode m β) =
          slimPiF3Hom m (aElt l) := by
      rw [slimPiF3Hom_aElt_eq_stableConj_rowLabel,
        slimPiF3Hom_aElt_eq_stableConj_rowLabel]
      rw [map_inv] at hright
      calc
        (of (slimGenCode m β))⁻¹ *
              CentralHNNFreeLabel.stableConj
                (slimLink m) (slimTransversal m)
                  (slimRowLabel m (bK f)) *
            of (slimGenCode m β) =
            (of (slimGenCode m β))⁻¹ *
              ((of (slimGenCode m β)) *
                CentralHNNFreeLabel.stableConj
                  (slimLink m) (slimTransversal m)
                    (slimRowLabel m (bK l)) *
                (of (slimGenCode m β))⁻¹) *
              of (slimGenCode m β) := by rw [hright']
        _ = CentralHNNFreeLabel.stableConj
              (slimLink m) (slimTransversal m)
                (slimRowLabel m (bK l)) := by group
    have hfTail := (slimGen_conj_aElt_mem_F3Range_iff hβ).mp
      ⟨aElt l, hpositive.symm⟩
    refine ⟨hfTail, ?_⟩
    have hcollapse :=
      slimGen_conj_aElt_eq_aElt_add_rightTail hβ hfTail
    apply aElt_injective
    apply slimPiF3Hom_injective m
    exact hpositive.symm.trans hcollapse
  · rintro ⟨hfTail, rfl⟩
    have hforward := slimRightLabel_rowLabel_eq hβ hfTail
    have hcomp := CentralHNNFreeLabel.rightLabel_comp
      (M := slimLink m) (slimTransversal m)
      (slimGenCode m β)⁻¹ (slimGenCode m β)
        (slimRowLabel m (bK f))
    rw [mul_inv_cancel,
      CentralHNNFreeLabel.rightLabel_one] at hcomp
    exact (congrArg
      (CentralHNNFreeLabel.rightLabel
        (M := slimLink m) (slimTransversal m) (slimGenCode m β)⁻¹)
      hforward).symm.trans hcomp

/-- The inverse transition preserves the Omega language: it removes the
selected zeroth block and leaves all other blocks unchanged. -/
theorem omega_mem_of_rightLabel_inv_rowLabel_eq
    {m : ℕ} (hm : 0 < m) {B : Set E} (h0 : (0 : E) ∈ B)
    {β l f : E} (hβ : β ∈ B ∩ blockSet m) (hl : l ∈ omegaOp m B)
    (hlabel : CentralHNNFreeLabel.rightLabel
        (M := slimLink m) (slimTransversal m) (slimGenCode m β)⁻¹
          (slimRowLabel m (bK l)) = slimRowLabel m (bK f)) :
    f ∈ omegaOp m B := by
  obtain ⟨hfTail, hlf⟩ :=
    (rightLabel_inv_rowLabel_eq_iff hβ.2).mp hlabel
  apply rightTail_mem_omegaOp_of_add hm h0 hβ.2 hfTail
  rwa [← hlf]

end Omega
end Higman
end GroupApproximation
