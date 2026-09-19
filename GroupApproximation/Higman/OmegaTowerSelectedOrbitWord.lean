import GroupApproximation.Higman.OmegaTowerSelectedCodeFree
import GroupApproximation.Higman.OmegaTowerStaticSeamOrbitKWord

/-!
# A returning orbit equation on the exact selected free alphabet

The block spelling produced by the link projection is supported on selected
blocks.  Reindexing it by the selected subtype turns subgroup membership into
an actual free word, so the final normal-form theorem can induct on its unique
reduced word without carrying closure proofs.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

def selectedBlockIncl (m : ℕ) (B : Set E) :
    SelectedBlock m B → ↥(blockSet m) :=
  fun β => ⟨(β : E), β.property.2⟩

theorem selectedBlockIncl_injective (m : ℕ) (B : Set E) :
    Function.Injective (selectedBlockIncl m B) := by
  intro β γ hβγ
  apply Subtype.ext
  exact congrArg (fun x : ↥(blockSet m) => (x : E)) hβγ

/-- The free-group inclusion of the selected alphabet has exactly the
selected block-word subgroup as its range. -/
theorem selectedBlockInclMap_range (m : ℕ) (B : Set E) :
    (FreeGroup.map (selectedBlockIncl m B)).range =
      Subgroup.closure (FreeGroup.of '' selectedBlocks m B) := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    induction w using FreeGroup.induction_on with
    | C1 =>
        rw [map_one]
        exact Subgroup.one_mem _
    | of β =>
        rw [FreeGroup.map.of]
        exact Subgroup.subset_closure
          ⟨selectedBlockIncl m B β, β.property.1, rfl⟩
    | inv_of β hβ =>
        rw [map_inv]
        exact Subgroup.inv_mem _ hβ
    | mul x y hx hy =>
        rw [map_mul]
        exact Subgroup.mul_mem _ hx hy
  · rw [Subgroup.closure_le]
    rintro _ ⟨β, hβ, rfl⟩
    let γ : SelectedBlock m B := ⟨(β : E), ⟨hβ, β.property⟩⟩
    exact ⟨FreeGroup.of γ,
      by simp only [FreeGroup.map.of, selectedBlockIncl, γ]⟩

noncomputable def selectedLinkHom (m : ℕ) (B : Set E) :
    FreeGroup (SelectedBlock m B) →* Cent3 (rowOut m) :=
  (slimLinkLift m).comp (FreeGroup.map (selectedBlockIncl m B))

noncomputable def selectedRowInvHom (m : ℕ) (B : Set E) :
    FreeGroup (SelectedBlock m B) →* ↥Conj.K :=
  (blockKInvHom m).comp (FreeGroup.map (selectedBlockIncl m B))

theorem selectedAHom_eq_blockAHom_comp (m : ℕ) (B : Set E) :
    selectedAHom m B =
      (blockAHom m).comp (FreeGroup.map (selectedBlockIncl m B)) := by
  refine FreeGroup.ext_hom _ _ fun β => ?_
  simp only [selectedAHom_of, MonoidHom.comp_apply, FreeGroup.map.of]
  simp [blockAHom, selectedBlockIncl]

/-- Final exact input to the reduced signed-word scan. -/
theorem exists_selected_orbit_word_of_rightLabel_rowLabel_eq
    {m : ℕ} {B : Set E} {g : Cent3 (rowOut m)} {l f : E}
    (hg : g ∈ slimGenSub m B)
    (hlabel : CentralHNNFreeLabel.rightLabel
        (M := slimLink m) (slimTransversal m) g
          (slimRowLabel m (bK l)) = slimRowLabel m (bK f)) :
    ∃ v : FreeGroup (SelectedBlock m B),
      selectedCodeHom m B v = g ∧
      selectedLinkHom m B v =
        slimBaseCode m l * g * (slimBaseCode m f)⁻¹ ∧
      selectedRowInvHom m B v = bK l * (bK f)⁻¹ := by
  obtain ⟨u, huSelected, huCode, huLink, huRow⟩ :=
    exists_selected_block_word_with_K_equation_of_rightLabel_rowLabel_eq
      hg hlabel
  have huRange : u ∈ (FreeGroup.map (selectedBlockIncl m B)).range := by
    rwa [selectedBlockInclMap_range]
  obtain ⟨v, rfl⟩ := huRange
  refine ⟨v, ?_, huLink, huRow⟩
  rw [selectedCodeHom, MonoidHom.comp_apply,
    selectedAHom_eq_blockAHom_comp, MonoidHom.comp_apply, huCode]

end Omega
end Higman
end GroupApproximation
