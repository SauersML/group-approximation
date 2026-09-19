import GroupApproximation.Higman.OmegaTowerStaticSeamOrbitWord

/-!
# Intrinsic row equation of a returning Omega orbit word

The row projection of the selected block spelling can be read inside the
original conjugator subgroup `K`.  This formulation is independent of the
three central-HNN carriers and is the exact endpoint consumed by a reduced
block-word normal-form argument.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

/-- Convert the row projection equation of a block spelling to the intrinsic
equation in the conjugator subgroup. -/
theorem blockKInvHom_eq_bK_mul_inv_of_blockRowInvHom_eq
    {m : ℕ} {u : FreeGroup ↥(blockSet m)} {l f : E}
    (hu : blockRowInvHom m u =
      Row.basisHom (elt l) * (Row.basisHom (elt f))⁻¹) :
    blockKInvHom m u = bK l * (bK f)⁻¹ := by
  apply Subtype.ext
  change ((blockKInvHom m u : ↥Conj.K) : F₃) =
    ((bK l : ↥Conj.K) : F₃) * (((bK f : ↥Conj.K) : F₃))⁻¹
  have hmap := DFunLike.congr_fun (Ksubtype_comp_blockKInvHom m) u
  change ((blockKInvHom m u : ↥Conj.K) : F₃) =
    rowIntoF3 (blockRowInvHom m u) at hmap
  rw [hu, map_mul, map_inv] at hmap
  have hl := DFunLike.congr_fun rowIntoF3_comp_basisHom (elt l)
  have hf := DFunLike.congr_fun rowIntoF3_comp_basisHom (elt f)
  change rowIntoF3 (Row.basisHom (elt l)) = rowHom (elt l) at hl
  change rowIntoF3 (Row.basisHom (elt f)) = rowHom (elt f) at hf
  rw [hl, hf] at hmap
  simpa only [bK, bElt] using hmap

/-- Fully intrinsic selected-word consequence of a returning orbit label. -/
theorem exists_selected_block_word_with_K_equation_of_rightLabel_rowLabel_eq
    {m : ℕ} {B : Set E} {g : Cent3 (rowOut m)} {l f : E}
    (hg : g ∈ slimGenSub m B)
    (hlabel : CentralHNNFreeLabel.rightLabel
        (M := slimLink m) (slimTransversal m) g
          (slimRowLabel m (bK l)) = slimRowLabel m (bK f)) :
    ∃ u : FreeGroup ↥(blockSet m),
      u ∈ Subgroup.closure (FreeGroup.of '' selectedBlocks m B) ∧
      genHom (rowOut m) (blockAHom m u) = g ∧
      slimLinkLift m u =
        slimBaseCode m l * g * (slimBaseCode m f)⁻¹ ∧
      blockKInvHom m u = bK l * (bK f)⁻¹ := by
  obtain ⟨u, huSelected, huCode, huLink, huRow⟩ :=
    exists_selected_block_word_of_rightLabel_rowLabel_eq hg hlabel
  exact ⟨u, huSelected,
    genHom_blockAHom_eq_of_selected_block_word hg huCode,
    huLink, blockKInvHom_eq_bK_mul_inv_of_blockRowInvHom_eq huRow⟩

end Omega
end Higman
end GroupApproximation
