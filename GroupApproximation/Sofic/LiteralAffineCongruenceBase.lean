import GroupApproximation.Monsters.LiteralBaseCompleteness
import GroupApproximation.Sofic.LiteralBaseTranslationLattice
import GroupApproximation.Kazhdan.TorsionFreeKazhdanPartner
import GroupApproximation.Algebra.FiniteResidual

/-!
# The torsion-free affine level-three base

The literal affine base is `ℤ³ ⋊ SL₃(ℤ)`.  Its full rotation factor has
torsion, which forces every map from the full base to a torsion-free group to
be trivial.  Here we replace that base by the inverse image of the principal
level-three congruence subgroup.  It is finite index, finitely presented and
Kazhdan, while its rotation quotient and translation kernel are both
torsion-free.
-/

namespace GroupApproximation
namespace LiteralAffineCongruenceBase

open LiteralNonMFPresentation
open LiteralBaseRelations
open LiteralBaseRotationRetract
open LiteralBaseP13RotationQuotient
open LiteralBaseCompleteness
open LiteralBaseTranslationNormal
open LiteralBaseTranslationLattice
open LiteralP13MatrixModel
open CongruenceSubgroup

noncomputable section

/-- The audited P13 quotient onto the three-generator rotation presentation
is injective as well as surjective. -/
theorem p13ToRotation_injective : Function.Injective p13ToRotation := by
  intro a b hab
  apply P13DescentMaster.toSL3_injective
  apply eq_of_mul_inv_eq_one
  apply blockEmbed4_eq_one
  rw [map_mul, map_inv]
  have ha := DFunLike.congr_fun rotationToMat_comp_p13ToRotation a
  have hb := DFunLike.congr_fun rotationToMat_comp_p13ToRotation b
  simp only [MonoidHom.comp_apply] at ha hb
  rw [← ha, ← hb, hab, mul_inv_cancel]

/-- The abstract eight-relator rotation group is exactly `SL₃(ℤ)`. -/
noncomputable def rotationEquivSL3 : Rotation ≃* SL3Z :=
  (MulEquiv.ofBijective p13ToRotation
    ⟨p13ToRotation_injective, p13ToRotation_surjective⟩).symm.trans
      P13DescentMaster.p13CompletenessEquiv

/-- The linear part of an affine-base element. -/
noncomputable def linearPart : Base →* SL3Z :=
  rotationEquivSL3.toMonoidHom.comp baseToRotation

theorem linearPart_surjective : Function.Surjective linearPart :=
  rotationEquivSL3.surjective.comp baseToRotation_surjective

instance gamma3_normal : gamma3.Normal := by
  dsimp [gamma3]
  infer_instance

/-- The affine level-three subgroup: translations together with rotations
congruent to the identity modulo three. -/
noncomputable def levelThree : Subgroup Base := gamma3.comap linearPart

/-- The carrier used by the corrected compression source. -/
abbrev P : Type := ↑levelThree

instance levelThree_normal : levelThree.Normal := by
  dsimp [levelThree]
  infer_instance

instance levelThree_finiteIndex : levelThree.FiniteIndex :=
  finiteIndex_comap_of_normal linearPart gamma3

/-- Each translation belongs to the affine congruence subgroup. -/
theorem translations_le_levelThree : translations ≤ levelThree := by
  intro g hg
  show linearPart g ∈ gamma3
  have hrot : baseToRotation g = 1 := by
    rw [← MonoidHom.mem_ker, baseToRotation_ker_eq_translations]
    exact hg
  rw [linearPart, MonoidHom.comp_apply, hrot, map_one]
  exact Subgroup.one_mem gamma3

theorem v1_mem_levelThree : LiteralBaseRelations.v1 ∈ levelThree :=
  translations_le_levelThree LiteralBaseTranslationNormal.v1_mem_translations

theorem v2_mem_levelThree : LiteralBaseRelations.v2 ∈ levelThree :=
  translations_le_levelThree LiteralBaseTranslationNormal.v2_mem_translations

theorem v3_mem_levelThree : LiteralBaseRelations.v3 ∈ levelThree :=
  translations_le_levelThree LiteralBaseTranslationNormal.v3_mem_translations

end

end LiteralAffineCongruenceBase
end GroupApproximation
