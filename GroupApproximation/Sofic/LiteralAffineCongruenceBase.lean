import GroupApproximation.Monsters.LiteralBaseCompleteness
import GroupApproximation.Sofic.LiteralBaseTranslationLattice
import GroupApproximation.Sofic.LiteralBaseP13PropertyTBridge
import GroupApproximation.Kazhdan.TorsionFreeKazhdanPartner
import GroupApproximation.Kazhdan.KazhdanFiniteIndex
import GroupApproximation.Algebra.FreeGroupFiniteRank
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

theorem v1_mem_levelThree : v1 ∈ levelThree :=
  translations_le_levelThree v1_mem_translations

theorem v2_mem_levelThree : v2 ∈ levelThree :=
  translations_le_levelThree v2_mem_translations

theorem v3_mem_levelThree : v3 ∈ levelThree :=
  translations_le_levelThree v3_mem_translations

/-- The integral translation lattice is torsion-free. -/
theorem lattice_isPowerTorsionFree :
    IsPowerTorsionFree (Multiplicative Lattice) := by
  intro a n hn hpow
  apply Multiplicative.toAdd.injective
  funext i
  have hi := congrArg (fun z : Multiplicative Lattice ↦ z.toAdd i) hpow
  simp only [toAdd_pow, toAdd_one, Pi.zero_apply, nsmul_eq_mul] at hi
  rcases mul_eq_zero.mp hi with hn0 | hai
  · exact absurd (Int.natCast_eq_zero.mp hn0) hn.ne'
  · exact hai

/-- The literal translation subgroup is torsion-free. -/
theorem translations_isPowerTorsionFree : IsPowerTorsionFree translations :=
  IsPowerTorsionFree.comap lattice_isPowerTorsionFree
    latticeEquivTranslations.symm.toMonoidHom
    latticeEquivTranslations.symm.injective

/-- The affine level-three subgroup is torsion-free.  A torsion element has
trivial image in `Γ(3)`, hence lies in the integral translation lattice. -/
theorem p_isPowerTorsionFree : IsPowerTorsionFree P := by
  intro g n hn hpow
  have hglinear : linearPart (g : Base) ∈ gamma3 := g.property
  let r : ↑gamma3 := ⟨linearPart g, hglinear⟩
  have hgpow : ((g : Base) ^ n) = 1 := congrArg Subtype.val hpow
  have hrpow : r ^ n = 1 := by
    apply Subtype.ext
    simpa [r] using congrArg linearPart hgpow
  have hrone : r = 1 := gamma3_torsionFree r n hn hrpow
  have hlin : linearPart (g : Base) = 1 := congrArg Subtype.val hrone
  have hrot : baseToRotation (g : Base) = 1 := by
    apply rotationEquivSL3.injective
    simpa [linearPart] using hlin
  have hgtrans : (g : Base) ∈ translations := by
    rw [← baseToRotation_ker_eq_translations, MonoidHom.mem_ker]
    exact hrot
  let t : translations := ⟨g, hgtrans⟩
  have htpow : t ^ n = 1 := by
    apply Subtype.ext
    exact hgpow
  have htone : t = 1 := translations_isPowerTorsionFree t n hn htpow
  apply Subtype.ext
  exact congrArg Subtype.val htone

/-- Finite presentation passes from the literal affine base to its
finite-index level-three subgroup. -/
theorem p_isFinitelyPresented : Group.IsFinitelyPresented P :=
  FiniteIndex.isFinitelyPresented_subgroup_of_finiteIndex' levelThree
    (inferInstance : Group.IsFinitelyPresented Base)

/-- Property `(T)` passes from the literal affine base to its finite-index
level-three subgroup. -/
theorem p_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} P :=
  FiniteIndex.hasKazhdanPropertyT_of_finiteIndex levelThree
    LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT

end

end LiteralAffineCongruenceBase
end GroupApproximation
