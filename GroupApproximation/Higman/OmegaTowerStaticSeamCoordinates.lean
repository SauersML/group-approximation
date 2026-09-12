import GroupApproximation.Higman.OmegaTowerStaticSeam

/-!
# Coordinates for the static Omega seam

These identities put the last static seam into the free kernel of the second
central HNN stage.  The original alphabet retracts onto exactly the selected
`g`-subgroup, while the desired Omega range is entirely in the kernel.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

/-- The base retraction of the stage-two alphabet is exactly the selected
first-stage `g`-subgroup. -/
theorem map_slimPiBaseRet_slimWBase (m : ℕ) (B : Set E) :
    (slimWBase m B).map (slimPiBaseRet m) = slimGenSub m B := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact slimPiBaseRet_mem_slimGenSub_of_mem_slimWBase hx
  · unfold slimGenSub
    rw [Subgroup.closure_le]
    rintro y ⟨β, hβ, rfl⟩
    refine ⟨slimPiOf m (slimGenCode m β), ?_, slimPiBaseRet_of m _⟩
    apply Subgroup.subset_closure
    exact Set.mem_union_right _ ⟨β, hβ, rfl⟩

/-- Every coded conjugate, hence every desired Omega-range element, is killed
by the stage-two base retraction. -/
theorem omegaRangeSub_le_slimPiBaseRet_ker (m : ℕ) (B : Set E) :
    omegaRangeSub m B ≤ (slimPiBaseRet m).ker := by
  rintro y ⟨x, hx, rfl⟩
  change slimPiBaseRet m (slimPiF3Hom m x) = 1
  unfold ASub at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨f, -, rfl⟩ := hx
      unfold aElt
      simp only [map_mul, map_inv, slimPiF3Hom_bElt, slimPiF3Hom_a,
        slimPiBaseRet_of, slimPiBaseRet_t, mul_one, inv_mul_cancel]
  | one => simp
  | mul x y _ _ hx hy => simp only [map_mul, hx, hy, mul_one]
  | inv x _ hx => simp only [map_inv, hx, inv_one]

/-- The desired range lies in the exact free-coordinate kernel identified by
`CentralHNNFreeLabel`. -/
theorem omegaRangeSub_le_stableConjLift_range (m : ℕ) (B : Set E) :
    omegaRangeSub m B ≤
      (CentralHNNFreeLabel.stableConjLift
        (slimLink m) (slimTransversal m)).range := by
  rw [CentralHNNFreeLabel.range_stableConjLift_eq_ker_baseRet,
    ← slimPiBaseRet_eq_freeLabelBaseRet]
  exact omegaRangeSub_le_slimPiBaseRet_ker m B

/-- The right-coset labels of the canonical Omega conjugators. -/
def omegaLabelSet (m : ℕ) (B : Set E) :
    Set (CentralHNNFreeLabel.Label (slimLink m) (slimTransversal m)) :=
  slimRowLabel m '' (bK '' omegaOp m B)

/-- The free coordinate subgroup on the canonical Omega labels. -/
def omegaLabelSub (m : ℕ) (B : Set E) :
    Subgroup (FreeGroup
      (CentralHNNFreeLabel.Label (slimLink m) (slimTransversal m))) :=
  Subgroup.closure (FreeGroup.of '' omegaLabelSet m B)

/-- A coded conjugate has exactly its canonical row-coset label in the free
kernel of the second central HNN stage. -/
theorem slimPiF3Hom_aElt_eq_stableConj_rowLabel (m : ℕ) (f : E) :
    slimPiF3Hom m (aElt f) =
      CentralHNNFreeLabel.stableConj
        (slimLink m) (slimTransversal m) (slimRowLabel m (bK f)) := by
  have h := DFunLike.congr_fun
    (slimPiF3Hom_comp_cbHom_eq_freeLabel m) (FreeGroup.of (bK f))
  calc
    slimPiF3Hom m (aElt f) =
        slimPiF3Hom m (Conj.cbHom (FreeGroup.of (bK f))) := by rw [aElt_eq]
    _ = CentralHNNFreeLabel.stableConjLift
          (slimLink m) (slimTransversal m)
            (slimLabelHom m (FreeGroup.of (bK f))) := h
    _ = CentralHNNFreeLabel.stableConj
          (slimLink m) (slimTransversal m) (slimRowLabel m (bK f)) := by
      simp only [slimLabelHom, FreeGroup.map.of,
        CentralHNNFreeLabel.stableConjLift, FreeGroup.lift_apply_of]
      rfl

/-- **Exact free-coordinate form of the desired Omega range.** -/
theorem omegaRangeSub_eq_map_omegaLabelSub (m : ℕ) (B : Set E) :
    omegaRangeSub m B =
      (omegaLabelSub m B).map
        (CentralHNNFreeLabel.stableConjLift
          (slimLink m) (slimTransversal m)) := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    unfold ASub at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨f, hf, rfl⟩ := hx
        refine ⟨FreeGroup.of (slimRowLabel m (bK f)), ?_, ?_⟩
        · apply Subgroup.subset_closure
          exact ⟨slimRowLabel m (bK f),
            ⟨bK f, ⟨f, hf, rfl⟩, rfl⟩, rfl⟩
        · simp only [CentralHNNFreeLabel.stableConjLift,
            FreeGroup.lift_apply_of]
          exact (slimPiF3Hom_aElt_eq_stableConj_rowLabel m f).symm
    | one => simp
    | mul x y _ _ hx hy => simpa only [map_mul] using Subgroup.mul_mem _ hx hy
    | inv x _ hx => simpa only [map_inv] using Subgroup.inv_mem _ hx
  · rintro y ⟨w, hw, rfl⟩
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨q, ⟨_, ⟨f, hf, rfl⟩, rfl⟩, rfl⟩ := hx
        refine ⟨aElt f, Subgroup.subset_closure ⟨f, hf, rfl⟩, ?_⟩
        simp only [CentralHNNFreeLabel.stableConjLift,
          FreeGroup.lift_apply_of]
        exact slimPiF3Hom_aElt_eq_stableConj_rowLabel m f
    | one => simp
    | mul x y _ _ hx hy => simpa only [map_mul] using Subgroup.mul_mem _ hx hy
    | inv x _ hx => simpa only [map_inv] using Subgroup.inv_mem _ hx

end Omega
end Higman
end GroupApproximation
