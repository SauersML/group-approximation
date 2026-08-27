import GroupApproximation.Higman.CentralHNNFreeLabelAffineCoordinates
import GroupApproximation.Higman.OmegaTowerRightLabel

/-!
# Affine scan of the static Omega join

The stage-two join is an instance of the generic affine free-label subgroup.
Consequently every element returning to the embedded `F₃` has a literal
conjugate-basis word whose row-label image lies in the concrete affine orbit
subgroup.  This removes all central-HNN bookkeeping from the remaining
matched-label normal-form argument.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq
open HNNExtension

theorem zero_mem_omegaOp_of_zero_mem {m : ℕ} {B : Set E}
    (h0 : (0 : E) ∈ B) : (0 : E) ∈ omegaOp m B := by
  intro i
  have hblock : blockAt m i (0 : E) = 0 := by
    apply Finsupp.ext
    intro j
    simp [blockAt_apply]
  rwa [hblock]

theorem slimRowLabel_zero (m : ℕ) :
    slimRowLabel m (bK (0 : E)) =
      (((slimTransversal m).compl (1 : ℤˣ)).equiv 1).2 := by
  unfold slimRowLabel
  rw [slimKBase_bK, slimBaseCode_zero]

/-- Once the zero sequence is allowed, every intrinsic label of the selected
base subgroup is already an orbit translate of the zero Omega label. -/
theorem labelSet_slimGenSub_le_omegaOrbit
    {m : ℕ} {B : Set E} (h0 : (0 : E) ∈ B) :
    CentralHNNFreeLabel.labelSet
        (slimLink m) (slimTransversal m) (slimGenSub m B) ⊆
      {q | ∃ g : Cent3 (rowOut m), g ∈ slimGenSub m B ∧
        ∃ r, r ∈ omegaLabelSet m B ∧
          q = CentralHNNFreeLabel.rightLabel
            (M := slimLink m) (slimTransversal m) g r} := by
  rintro q ⟨g, hg, rfl⟩
  refine ⟨g, hg, slimRowLabel m (bK (0 : E)), ?_, ?_⟩
  · exact ⟨bK (0 : E),
      ⟨0, zero_mem_omegaOp_of_zero_mem h0, rfl⟩, rfl⟩
  · rw [slimRowLabel_zero,
      CentralHNNFreeLabel.rightLabel_labelOf, one_mul]

/-- The concrete static join is exactly the generic affine generated
subgroup. -/
theorem slimJoin_eq_affineGenerated (m : ℕ) (B : Set E) :
    slimWBase m B ⊔ omegaRangeSub m B =
      CentralHNNFreeLabel.affineGeneratedSub
        (slimLink m) (slimTransversal m) (slimGenSub m B)
          (omegaLabelSub m B) := by
  rw [CentralHNNFreeLabel.affineGeneratedSub_eq,
    ← slimWBase_eq_innerClosure, ← omegaRangeSub_eq_map_omegaLabelSub]

/-- Base and free-coordinate invariants for every word in the static join. -/
theorem slimJoin_affine_invariant {m : ℕ} {B : Set E} {z : SlimPi m}
    (hz : z ∈ slimWBase m B ⊔ omegaRangeSub m B) :
    slimPiBaseRet m z ∈ slimGenSub m B ∧
      CentralHNNFreeLabel.freeCoord
          (slimLink m) (slimTransversal m) z ∈
        CentralHNNFreeLabel.affineCoordSub
          (slimLink m) (slimTransversal m) (slimGenSub m B)
            (omegaLabelSub m B) := by
  rw [slimJoin_eq_affineGenerated] at hz
  simpa only [slimPiBaseRet_eq_freeLabelBaseRet] using
    CentralHNNFreeLabel.baseRet_mem_and_freeCoord_mem_of_mem_affineGeneratedSub
      (slimLink m) (slimTransversal m) (slimGenSub m B)
        (omegaLabelSub m B) hz

/-- The affine invariant meets the embedded row coordinates only on the
literal intersection of the affine orbit alphabet with the row alphabet. -/
theorem slimAffineCoord_inf_rows_le (m : ℕ) (B : Set E) :
    CentralHNNFreeLabel.affineCoordSub
          (slimLink m) (slimTransversal m) (slimGenSub m B)
            (omegaLabelSub m B) ⊓
        Subgroup.closure (FreeGroup.of '' Set.range (slimRowLabel m)) ≤
      Subgroup.closure (FreeGroup.of ''
        (CentralHNNFreeLabel.affineLabelSet
            (slimLink m) (slimTransversal m) (slimGenSub m B)
              (omegaLabelSet m B) ∩
          Set.range (slimRowLabel m))) := by
  change CentralHNNFreeLabel.affineCoordSub
          (slimLink m) (slimTransversal m) (slimGenSub m B)
            (Subgroup.closure (FreeGroup.of '' omegaLabelSet m B)) ⊓
        Subgroup.closure (FreeGroup.of '' Set.range (slimRowLabel m)) ≤ _
  exact CentralHNNFreeLabel.affineCoordSub_inf_closure_le
    (slimLink m) (slimTransversal m) (slimGenSub m B)
      (omegaLabelSet m B) (Set.range (slimRowLabel m))

/-- An element of the static join which returns to the embedded `F₃` has a
conjugate-basis spelling supported in the exact affine coordinate subgroup. -/
theorem exists_affine_cbWord_of_mem_slimJoin_range
    {m : ℕ} {B : Set E} {z : SlimPi m}
    (hzJoin : z ∈ slimWBase m B ⊔ omegaRangeSub m B)
    (hzRange : z ∈ (slimPiF3Hom m).range) :
    ∃ v : FreeGroup ↥Conj.K,
      z = slimPiF3Hom m (Conj.cbHom v) ∧
      slimLabelHom m v ∈
        CentralHNNFreeLabel.affineCoordSub
          (slimLink m) (slimTransversal m) (slimGenSub m B)
            (omegaLabelSub m B) := by
  obtain ⟨x, rfl⟩ := hzRange
  have hinv := slimJoin_affine_invariant hzJoin
  have hkill : genProjection3 m
      (slimPiBaseRet m (slimPiF3Hom m x)) = 1 := by
    change ((genProjection3 m).comp
      ((slimPiBaseRet m).comp (slimPiF3Hom m))) x = 1
    rw [genProjection3_slimPiBaseRet_comp_slimPiF3Hom]
    rfl
  have hbase : slimPiBaseRet m (slimPiF3Hom m x) = 1 :=
    eq_one_of_mem_slimGenSub_of_genProjection3_eq_one hinv.1 hkill
  obtain ⟨v, hv⟩ := exists_cbWord_of_slimPiF3Hom_baseRet_eq_one hbase
  refine ⟨v, by rw [hv], ?_⟩
  have hfree := DFunLike.congr_fun
    (slimPiF3Hom_comp_cbHom_eq_freeLabel m) v
  change slimPiF3Hom m (Conj.cbHom v) =
    CentralHNNFreeLabel.stableConjLift
      (slimLink m) (slimTransversal m) (slimLabelHom m v) at hfree
  have hcoord : CentralHNNFreeLabel.freeCoord
      (slimLink m) (slimTransversal m)
        (slimPiF3Hom m (Conj.cbHom v)) = slimLabelHom m v := by
    rw [hfree]
    exact CentralHNNFreeLabel.freeCoord_stableConjLift
      (slimLink m) (slimTransversal m) (slimLabelHom m v)
  rw [← hcoord, hv]
  exact hinv.2

/-- Strongest unconditional alphabet form of the static scan: the resulting
row-label word is supported on the literal affine-orbit/row intersection. -/
theorem exists_boundary_cbWord_of_mem_slimJoin_range
    {m : ℕ} {B : Set E} {z : SlimPi m}
    (hzJoin : z ∈ slimWBase m B ⊔ omegaRangeSub m B)
    (hzRange : z ∈ (slimPiF3Hom m).range) :
    ∃ v : FreeGroup ↥Conj.K,
      z = slimPiF3Hom m (Conj.cbHom v) ∧
      slimLabelHom m v ∈ Subgroup.closure (FreeGroup.of ''
        (CentralHNNFreeLabel.affineLabelSet
            (slimLink m) (slimTransversal m) (slimGenSub m B)
              (omegaLabelSet m B) ∩
          Set.range (slimRowLabel m))) := by
  obtain ⟨v, hzv, hvAffine⟩ :=
    exists_affine_cbWord_of_mem_slimJoin_range hzJoin hzRange
  refine ⟨v, hzv, slimAffineCoord_inf_rows_le m B ⟨hvAffine, ?_⟩⟩
  have hvRows := CentralHNNFreeLabel.Coordinate.map_mem_closure_range
    (slimLabelIndex m) v
  change slimLabelHom m v ∈
    Subgroup.closure (FreeGroup.of '' Set.range (slimLabelIndex m))
  exact hvRows

end Omega
end Higman
end GroupApproximation
