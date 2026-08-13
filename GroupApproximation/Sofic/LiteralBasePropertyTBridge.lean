import GroupApproximation.Sofic.LiteralTranslationOrbit
import GroupApproximation.Sofic.LiteralBaseRotationRetract
import GroupApproximation.Kazhdan.HilbertConvexFixedPoint

/-!
# Property (T) transfer from the literal rotation group to the affine base

The literal affine base is the internal semidirect product of its translation
lattice by its rotation subgroup.  This file proves, entirely from the printed
relations, that property `(T)` of the abstract eight-relator rotation group
implies property `(T)` of the full twenty-relator base.

The key point is stronger than the usual extension permanence argument.  Once
a vector has been projected to the rotation-fixed subspace, every translation
moves it by a uniformly bounded amount: the two-conjugate normal form from
`LiteralTranslationOrbit` makes that bound independent of the lattice vector.
The bounded-orbit fixed-point theorem then projects once more to a vector fixed
by both subgroups.  Thus the only remaining property-`(T)` input for the
literal base is the rotation presentation itself.
-/

namespace GroupApproximation
namespace LiteralBasePropertyTBridge

open LiteralNonMFPresentation
open LiteralBaseRelations LiteralBaseTranslationNormal
open LiteralBaseRotationRetract LiteralTranslationOrbit

noncomputable section

private abbrev Base := LiteralNonMFPresentation.Base

local instance : DecidableEq Base := Classical.decEq Base
local instance : DecidableEq rotations := Classical.decEq rotations

private def baseControlSet (S : Finset rotations) : Finset Base :=
  (S.image fun r ↦ (r : Base)) ∪ {v2, v3}

private theorem mem_baseControlSet_of_mem {S : Finset rotations}
    {r : rotations} (hr : r ∈ S) : (r : Base) ∈ baseControlSet S := by
  exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hr)

private theorem v2_mem_baseControlSet (S : Finset rotations) :
    v2 ∈ baseControlSet S := by
  simp [baseControlSet]

private theorem v3_mem_baseControlSet (S : Finset rotations) :
    v3 ∈ baseControlSet S := by
  simp [baseControlSet]

private theorem norm_displacement_at_near
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : Base →* (E ≃ₗᵢ[ℝ] E)) (g : Base) (x p : E) :
    ‖rho g p - p‖ ≤ ‖rho g x - x‖ + 2 * ‖p - x‖ := by
  have hid : rho g p - p =
      rho g (p - x) + (rho g x - x) + (x - p) := by
    rw [map_sub]
    abel
  rw [hid]
  calc
    ‖rho g (p - x) + (rho g x - x) + (x - p)‖ ≤
        ‖rho g (p - x)‖ + ‖rho g x - x‖ + ‖x - p‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add_right (norm_add_le _ _) _)
    _ = ‖rho g x - x‖ + 2 * ‖p - x‖ := by
      rw [(rho g).norm_map, norm_sub_rev]
      ring

private theorem movingProjection_norm_lt_one_div_sixtyFour
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {S : Finset rotations} {kappa : ℝ}
    (hS : IsKazhdanPair rotations S kappa) (hkappaOne : kappa ≤ 1)
    (rho : Base →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (hnear : ∀ q ∈ baseControlSet S,
      ‖rho q x - x‖ < kappa / 64) :
    ‖KazhdanFixedSpace.subgroupMovingProjection rho rotations x‖ < 1 / 64 := by
  let m : E := KazhdanFixedSpace.subgroupMovingProjection rho rotations x
  have hmMem : m ∈ KazhdanFixedSpace.subgroupMovingSubspace rho rotations :=
    KazhdanFixedSpace.subgroupMovingProjection_mem rho rotations x
  by_cases hm : m = 0
  · rw [hm, norm_zero]
    norm_num
  · let w : KazhdanFixedSpace.subgroupMovingSubspace rho rotations := ⟨m, hmMem⟩
    have hw : w ≠ 0 := by
      intro hw
      apply hm
      exact congrArg Subtype.val hw
    obtain ⟨q, hqS, hmove⟩ :=
      hS.exists_moved_mul_norm_of_noInvariant
        (KazhdanFixedSpace.subgroupMovingRepresentation rho rotations)
        (KazhdanFixedSpace.subgroupMovingRepresentation_hasNoInvariantVectors
          rho rotations) w hw
    have hprojected :
        ‖rho (q : Base) m - m‖ ≤ ‖rho (q : Base) x - x‖ :=
      KazhdanFixedSpace.norm_subgroupMovingProjection_displacement_le_of_mem_normalizer
        rho rotations (rotations.le_normalizer q.2) x
    have hsmall : ‖rho (q : Base) x - x‖ < kappa / 64 :=
      hnear (q : Base) (mem_baseControlSet_of_mem hqS)
    have hgap : kappa * ‖m‖ ≤ ‖rho (q : Base) m - m‖ := by
      simpa [w, m] using hmove
    have hkappa : 0 < kappa := hS.1
    nlinarith [hgap.trans_lt (hprojected.trans_lt hsmall)]

private theorem exists_global_fixed_near
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {S : Finset rotations} {kappa : ℝ}
    (hS : IsKazhdanPair rotations S kappa) (hkappaOne : kappa ≤ 1)
    (rho : Base →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (hnear : ∀ q ∈ baseControlSet S,
      ‖rho q x - x‖ < kappa / 64) :
    ∃ y : E, (∀ g : Base, rho g y = y) ∧ ‖y - x‖ < 1 := by
  let p : E := KazhdanFixedSpace.fixedProjection rho rotations x
  let m : E := KazhdanFixedSpace.subgroupMovingProjection rho rotations x
  have hm : ‖m‖ < 1 / 64 :=
    movingProjection_norm_lt_one_div_sixtyFour hS hkappaOne rho x hnear
  have hpx : ‖p - x‖ = ‖m‖ := by
    rw [KazhdanFixedSpace.subgroupMovingProjection_eq_sub_fixedProjection]
    change ‖p - x‖ = ‖x - p‖
    exact norm_sub_rev _ _
  have hpRot : p ∈ KazhdanFixedSpace.fixedSubspace rho rotations :=
    (KazhdanFixedSpace.fixedProjection rho rotations x).property
  have hpFixed : ∀ r : rotations, rho (r : Base) p = p := by
    intro r
    exact (KazhdanFixedSpace.mem_fixedSubspace_iff rho rotations p).mp
      hpRot r r.2
  have hkappa64 : kappa / 64 ≤ 1 / 64 := by nlinarith
  have hv2x : ‖rho v2 x - x‖ < kappa / 64 :=
    hnear v2 (v2_mem_baseControlSet S)
  have hv3x : ‖rho v3 x - x‖ < kappa / 64 :=
    hnear v3 (v3_mem_baseControlSet S)
  have hv2p : ‖rho v2 p - p‖ < 3 / 64 := by
    have h := norm_displacement_at_near rho v2 x p
    rw [hpx] at h
    nlinarith
  have hv3p : ‖rho v3 p - p‖ < 3 / 64 := by
    have h := norm_displacement_at_near rho v3 x p
    rw [hpx] at h
    nlinarith
  have htranslation : ∀ t : translations, ‖rho t.1 p - p‖ ≤ 1 / 8 := by
    intro t
    have h := norm_translation_displacement_le_of_rotations_fixed
      rho p hpFixed t.2
    nlinarith
  obtain ⟨z, hzTrans, hzp⟩ :=
    HilbertConvexFixedPoint.exists_near_fixedSubspace
      rho translations p htranslation
  let y : E := KazhdanFixedSpace.fixedProjection rho translations p
  have hyTrans : y ∈ KazhdanFixedSpace.fixedSubspace rho translations :=
    (KazhdanFixedSpace.fixedProjection rho translations p).property
  have hRotNormalizes :
      rotations ≤ Subgroup.normalizer (translations : Set Base) := by
    rw [normalizer_translations_eq_top]
    exact le_top
  have hySup : y ∈
      KazhdanFixedSpace.fixedSubspace rho (translations ⊔ rotations) := by
    have heq := KazhdanFixedSpace.fixedProjection_eq_sup_of_fixed_of_normalizes
      rho translations rotations hRotNormalizes hpRot
    change (KazhdanFixedSpace.fixedProjection rho translations p : E) ∈
      KazhdanFixedSpace.fixedSubspace rho (translations ⊔ rotations)
    rw [heq]
    exact (KazhdanFixedSpace.fixedProjection rho
      (translations ⊔ rotations) p).property
  have hyGlobal : ∀ g : Base, rho g y = y := by
    intro g
    apply (KazhdanFixedSpace.mem_fixedSubspace_iff rho
      (translations ⊔ rotations) y).mp hySup
    rw [translations_sup_rotations]
    exact Subgroup.mem_top g
  have hyp : ‖y - p‖ ≤ 1 / 8 := by
    let U := KazhdanFixedSpace.fixedSubspace rho translations
    letI : CompleteSpace U :=
      (KazhdanFixedSpace.isClosed_fixedSubspace rho translations).completeSpace_coe
    have hmin : ‖p - y‖ ≤ ‖p - z‖ := by
      change ‖p - U.starProjection p‖ ≤ ‖p - z‖
      rw [U.starProjection_minimal]
      exact ciInf_le
        ⟨0, Set.forall_mem_range.mpr fun u : U ↦ norm_nonneg (p - (u : E))⟩
        ⟨z, hzTrans⟩
    rw [norm_sub_rev] at hmin ⊢
    exact hmin.trans hzp
  refine ⟨y, hyGlobal, ?_⟩
  calc
    ‖y - x‖ = ‖(y - p) + (p - x)‖ := by congr 1 <;> abel
    _ ≤ ‖y - p‖ + ‖p - x‖ := norm_add_le _ _
    _ < 1 := by rw [hpx]; nlinarith

/-- **Exact affine property-`(T)` reduction.**  If the abstract rotation
presentation has property `(T)`, then the literal twenty-relator affine base
has property `(T)`.

No relative-property-`(T)` theorem is assumed: the translation control is
proved intrinsically from the printed conjugation relations.  Consequently
the only remaining task for an unconditional property-`(T)` theorem for the
literal base is property `(T)` of `LiteralBaseRotationRetract.Rotation`. -/
theorem base_hasKazhdanPropertyT_of_rotation
    (hRotation : HasKazhdanPropertyT.{0, 0} Rotation) :
    HasKazhdanPropertyT.{0, 0} Base := by
  have hRotations : HasKazhdanPropertyT.{0, 0} rotations :=
    HasKazhdanPropertyT.of_mulEquiv rotationEquivRotations.symm hRotation
  obtain ⟨S, kappa, -, hkappa, hkappaOne, hS⟩ :=
    hRotations.exists_identity_pair
  refine ⟨baseControlSet S, kappa / 64, by positivity, ?_⟩
  intro E _ _ _ rho x hx hnear
  obtain ⟨y, hyFixed, hyNear⟩ :=
    exists_global_fixed_near hS hkappaOne rho x hnear
  have hy : y ≠ 0 := by
    intro hy0
    rw [hy0, zero_sub, norm_neg, hx] at hyNear
    linarith
  exact ⟨y, hy, hyFixed⟩

end

end LiteralBasePropertyTBridge
end GroupApproximation
