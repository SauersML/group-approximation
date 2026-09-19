import GroupApproximation.Higman.OmegaTowerStaticSeamOrbit

/-!
# The selected block word behind a returning Omega orbit label

The remaining static-seam assertion is a first-stage normal-form statement.
This file removes the transversal and subgroup-existence wrappers from that
statement.  A row label translated by an arbitrary selected code word returns
to the row alphabet only if a literal word in selected window blocks spells
the corresponding link element.  Both projections of that spelling are
recorded exactly: its code projection is the selected code word, and its row
projection is the quotient of the two canonical row words.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

/-- Right translation between two canonical row labels is exactly the
corresponding link-subgroup equation. -/
theorem rightLabel_rowLabel_eq_iff_link
    (m : ℕ) (g : Cent3 (rowOut m)) (l f : E) :
    CentralHNNFreeLabel.rightLabel
        (M := slimLink m) (slimTransversal m) g
          (slimRowLabel m (bK l)) = slimRowLabel m (bK f) ↔
      slimBaseCode m l * g * (slimBaseCode m f)⁻¹ ∈ slimLink m := by
  unfold slimRowLabel
  rw [CentralHNNFreeLabel.rightLabel_labelOf]
  change (((slimTransversal m).compl (1 : ℤˣ)).equiv
      (slimKBase m (bK l) * g)).2 =
        (((slimTransversal m).compl (1 : ℤˣ)).equiv
          (slimKBase m (bK f))).2 ↔ _
  rw [slimKBase_bK, slimKBase_bK]
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using
    (FiniteHNNFreeLabelAction.source_transversal_eq_iff
      (A := slimLink m) (B := slimLink m) (slimTransversal m)
      (slimBaseCode m l * g * (slimBaseCode m f)⁻¹)
      (slimBaseCode m f))

/-- On the selected code subgroup, `genProjection3` is the inverse of the
embedded second-copy map. -/
theorem genHom_genProjection3_eq_of_mem_slimGenSub
    {m : ℕ} {B : Set E} {g : Cent3 (rowOut m)}
    (hg : g ∈ slimGenSub m B) :
    genHom (rowOut m) (genProjection3 m g) = g := by
  rw [slimGenSub_eq_map_ASub] at hg
  obtain ⟨x, _hx, rfl⟩ := hg
  have hx := DFunLike.congr_fun (genProjection3_comp_genHom m) x
  simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using congrArg
    (genHom (rowOut m)) hx

/-- A returning orbit label has a literal selected-block spelling.  The last
two equalities retain all noncommutative information needed by the remaining
normal-form induction. -/
theorem exists_selected_block_word_of_rightLabel_rowLabel_eq
    {m : ℕ} {B : Set E} {g : Cent3 (rowOut m)} {l f : E}
    (hg : g ∈ slimGenSub m B)
    (hlabel : CentralHNNFreeLabel.rightLabel
        (M := slimLink m) (slimTransversal m) g
          (slimRowLabel m (bK l)) = slimRowLabel m (bK f)) :
    ∃ u : FreeGroup ↥(blockSet m),
      u ∈ Subgroup.closure (FreeGroup.of '' selectedBlocks m B) ∧
      blockAHom m u = genProjection3 m g ∧
      slimLinkLift m u =
        slimBaseCode m l * g * (slimBaseCode m f)⁻¹ ∧
      blockRowInvHom m u =
        Row.basisHom (elt l) * (Row.basisHom (elt f))⁻¹ := by
  have hlink :=
    (rightLabel_rowLabel_eq_iff_link m g l f).mp hlabel
  rw [← slimLinkLift_range m] at hlink
  obtain ⟨u, hu⟩ := hlink
  have hcode : blockAHom m u = genProjection3 m g := by
    rw [← genProjection3_comp_slimLinkLift m, MonoidHom.comp_apply, hu]
    simp only [map_mul, map_inv, genProjection3_emb3, slimBaseCode,
      inv_one, one_mul, mul_one]
  have hselected :
      u ∈ Subgroup.closure (FreeGroup.of '' selectedBlocks m B) := by
    apply mem_closure_selectedBlocks_of_blockAHom_mem
    rw [hcode]
    exact genProjection3_mem_ASub_of_mem_slimGenSub hg
  have hrow : blockRowInvHom m u =
      Row.basisHom (elt l) * (Row.basisHom (elt f))⁻¹ := by
    rw [← baseRet3_comp_slimLinkLift m, MonoidHom.comp_apply, hu]
    simp only [map_mul, map_inv, baseRet3_emb3, slimBaseCode,
      baseRet3_eq_one_of_mem_slimGenSub hg, mul_one]
  exact ⟨u, hselected, hcode, hu, hrow⟩

/-- The selected code word in the returning-label equation is not merely
projection-compatible: it reconstructs the original first-stage element. -/
theorem genHom_blockAHom_eq_of_selected_block_word
    {m : ℕ} {B : Set E} {g : Cent3 (rowOut m)}
    (hg : g ∈ slimGenSub m B) {u : FreeGroup ↥(blockSet m)}
    (hu : blockAHom m u = genProjection3 m g) :
    genHom (rowOut m) (blockAHom m u) = g := by
  rw [hu]
  exact genHom_genProjection3_eq_of_mem_slimGenSub hg

end Omega
end Higman
end GroupApproximation
