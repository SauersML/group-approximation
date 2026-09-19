import GroupApproximation.Sofic.LiteralBaseTranslationNormal
import Mathlib.GroupTheory.SemidirectProduct

/-!
# The CRW rotation presentation is a retract of the literal affine base

This file separates the three rotation letters from the three translations.
The standalone eight-relator rotation presentation maps into the literal
base.  Conversely, killing all translations defines a retraction from the
literal base.  Hence the rotation presentation embeds in the literal base,
independently of any completeness claim about its matrix realization.
-/

namespace GroupApproximation
namespace LiteralBaseRotationRetract

open LiteralBaseRelations LiteralBaseTranslationNormal
open LiteralNonMFPresentation hiding x y z v1 v2 v3

noncomputable section

local instance rotationDecidableEq {α : Type*} : DecidableEq α :=
  Classical.decEq α

abbrev RotationGenerator := Fin 3
abbrev rx : FreeGroup RotationGenerator := FreeGroup.of 0
abbrev ry : FreeGroup RotationGenerator := FreeGroup.of 1
abbrev rz : FreeGroup RotationGenerator := FreeGroup.of 2

abbrev relXCube : FreeGroup RotationGenerator := rx ^ 3
abbrev relYCube : FreeGroup RotationGenerator := ry ^ 3
abbrev relZSq : FreeGroup RotationGenerator := rz ^ 2
abbrev relXZCube : FreeGroup RotationGenerator := (rx * rz) ^ 3
abbrev relYZCube : FreeGroup RotationGenerator := (ry * rz) ^ 3
abbrev relXInvZXY : FreeGroup RotationGenerator :=
  (rx⁻¹ * rz * rx * ry) ^ 2
abbrev relYInvZYX : FreeGroup RotationGenerator :=
  (ry⁻¹ * rz * ry * rx) ^ 2
abbrev relXYSix : FreeGroup RotationGenerator := (rx * ry) ^ 6

noncomputable def rotationRelators : Finset (FreeGroup RotationGenerator) :=
  [relXCube, relYCube, relZSq, relXZCube, relYZCube,
    relXInvZXY, relYInvZYX, relXYSix].toFinset

/-- Stable indexed interface to the eight printed rotation relators.  It is
used by proof-carrying finite relator replays. -/
def rotationRelator : Fin 8 → FreeGroup RotationGenerator
  | 0 => relXCube
  | 1 => relYCube
  | 2 => relZSq
  | 3 => relXZCube
  | 4 => relYZCube
  | 5 => relXInvZXY
  | 6 => relYInvZYX
  | 7 => relXYSix

@[simp] theorem rotationRelator_mem (i : Fin 8) :
    rotationRelator i ∈ rotationRelators := by
  fin_cases i <;> simp [rotationRelator, rotationRelators]

theorem mem_rotationRelators_iff (r : FreeGroup RotationGenerator) :
    r ∈ rotationRelators ↔
      r = relXCube ∨ r = relYCube ∨ r = relZSq ∨
      r = relXZCube ∨ r = relYZCube ∨ r = relXInvZXY ∨
      r = relYInvZYX ∨ r = relXYSix := by
  simp [rotationRelators]

/-- The abstract three-generator group with exactly the eight printed CRW
rotation relators. -/
abbrev Rotation : Type :=
  PresentedGroup (rotationRelators : Set (FreeGroup RotationGenerator))

instance rotation_finitelyPresented : Group.IsFinitelyPresented Rotation :=
  inferInstance

abbrev rotationWord : FreeGroup RotationGenerator →* Rotation :=
  PresentedGroup.mk (rotationRelators : Set (FreeGroup RotationGenerator))

@[simp] theorem rotationWord_of (i : RotationGenerator) :
    rotationWord (FreeGroup.of i) = PresentedGroup.of i := rfl

abbrev X : Rotation := PresentedGroup.of 0
abbrev Y : Rotation := PresentedGroup.of 1
abbrev Z : Rotation := PresentedGroup.of 2

theorem rotationRelator_eq_one {r : FreeGroup RotationGenerator}
    (hr : r ∈ rotationRelators) : rotationWord r = 1 :=
  PresentedGroup.one_of_mem (Finset.mem_coe.mpr hr)

@[simp] theorem rotation_x_cube : X ^ 3 = 1 := by
  simpa only [relXCube, map_pow, rotationWord_of] using
    rotationRelator_eq_one (show relXCube ∈ rotationRelators by
      simp [rotationRelators])

@[simp] theorem rotation_y_cube : Y ^ 3 = 1 := by
  simpa only [relYCube, map_pow, rotationWord_of] using
    rotationRelator_eq_one (show relYCube ∈ rotationRelators by
      simp [rotationRelators])

@[simp] theorem rotation_z_sq : Z ^ 2 = 1 := by
  simpa only [relZSq, map_pow, rotationWord_of] using
    rotationRelator_eq_one (show relZSq ∈ rotationRelators by
      simp [rotationRelators])

@[simp] theorem rotation_xz_cube : (X * Z) ^ 3 = 1 := by
  simpa only [relXZCube, map_pow, map_mul, rotationWord_of] using
    rotationRelator_eq_one (show relXZCube ∈ rotationRelators by
      simp [rotationRelators])

@[simp] theorem rotation_yz_cube : (Y * Z) ^ 3 = 1 := by
  simpa only [relYZCube, map_pow, map_mul, rotationWord_of] using
    rotationRelator_eq_one (show relYZCube ∈ rotationRelators by
      simp [rotationRelators])

@[simp] theorem rotation_x_inv_z_x_y_sq : (X⁻¹ * Z * X * Y) ^ 2 = 1 := by
  simpa only [relXInvZXY, map_pow, map_mul, map_inv, rotationWord_of] using
    rotationRelator_eq_one (show relXInvZXY ∈ rotationRelators by
      simp [rotationRelators])

@[simp] theorem rotation_y_inv_z_y_x_sq : (Y⁻¹ * Z * Y * X) ^ 2 = 1 := by
  simpa only [relYInvZYX, map_pow, map_mul, map_inv, rotationWord_of] using
    rotationRelator_eq_one (show relYInvZYX ∈ rotationRelators by
      simp [rotationRelators])

@[simp] theorem rotation_xy_six : (X * Y) ^ 6 = 1 := by
  simpa only [relXYSix, map_pow, map_mul, rotationWord_of] using
    rotationRelator_eq_one (show relXYSix ∈ rotationRelators by
      simp [rotationRelators])

/-- Send the three abstract rotation generators to the three literal
rotation generators. -/
def rotationGeneratorToBase : RotationGenerator → Base
  | 0 => x
  | 1 => y
  | 2 => z

theorem rotationGeneratorToBase_kills :
    ∀ r ∈ rotationRelators,
      FreeGroup.lift rotationGeneratorToBase r = 1 := by
  intro r hr
  rw [mem_rotationRelators_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [map_pow, FreeGroup.lift_apply_of, rotationGeneratorToBase] using x_cube
  · simpa only [map_pow, FreeGroup.lift_apply_of, rotationGeneratorToBase] using y_cube
  · simpa only [map_pow, FreeGroup.lift_apply_of, rotationGeneratorToBase] using z_sq
  · simpa only [map_pow, map_mul, FreeGroup.lift_apply_of,
      rotationGeneratorToBase] using xz_cube
  · simpa only [map_pow, map_mul, FreeGroup.lift_apply_of,
      rotationGeneratorToBase] using yz_cube
  · simpa only [map_pow, map_mul, map_inv, FreeGroup.lift_apply_of,
      rotationGeneratorToBase] using x_inv_z_x_y_sq
  · simpa only [map_pow, map_mul, map_inv, FreeGroup.lift_apply_of,
      rotationGeneratorToBase] using y_inv_z_y_x_sq
  · simpa only [map_pow, map_mul, FreeGroup.lift_apply_of,
      rotationGeneratorToBase] using xy_six

/-- The canonical homomorphism from the abstract rotation presentation into
the literal affine base. -/
def rotationToBase : Rotation →* Base :=
  PresentedGroup.toGroup rotationGeneratorToBase_kills

@[simp] theorem rotationToBase_X : rotationToBase X = x := by
  simp [rotationToBase, rotationGeneratorToBase]

@[simp] theorem rotationToBase_Y : rotationToBase Y = y := by
  simp [rotationToBase, rotationGeneratorToBase]

@[simp] theorem rotationToBase_Z : rotationToBase Z = z := by
  simp [rotationToBase, rotationGeneratorToBase]

/-- Kill translations and retain the three rotation generators. -/
def baseGeneratorToRotation : BaseGenerator → Rotation
  | 0 | 1 | 2 => 1
  | 3 => X
  | 4 => Y
  | 5 => Z

theorem baseGeneratorToRotation_kills :
    ∀ r ∈ baseRelators,
      FreeGroup.lift baseGeneratorToRotation r = 1 := by
  intro r hr
  rw [mem_baseRelators_iff] at hr
  rcases hr with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [baseGeneratorToRotation, commutatorWord]

/-- The retraction which kills the translation subgroup. -/
def baseToRotation : Base →* Rotation :=
  PresentedGroup.toGroup baseGeneratorToRotation_kills

@[simp] theorem baseToRotation_v1 : baseToRotation v1 = 1 := by
  simp [baseToRotation, baseGeneratorToRotation]

@[simp] theorem baseToRotation_v2 : baseToRotation v2 = 1 := by
  simp [baseToRotation, baseGeneratorToRotation]

@[simp] theorem baseToRotation_v3 : baseToRotation v3 = 1 := by
  simp [baseToRotation, baseGeneratorToRotation]

@[simp] theorem baseToRotation_x : baseToRotation x = X := by
  simp [baseToRotation, baseGeneratorToRotation]

@[simp] theorem baseToRotation_y : baseToRotation y = Y := by
  simp [baseToRotation, baseGeneratorToRotation]

@[simp] theorem baseToRotation_z : baseToRotation z = Z := by
  simp [baseToRotation, baseGeneratorToRotation]

/-- The two canonical maps compose to the identity on the abstract rotation
presentation. -/
theorem baseToRotation_comp_rotationToBase :
    baseToRotation.comp rotationToBase = MonoidHom.id Rotation := by
  apply MonoidHom.ext
  intro r
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective
    (rotationRelators : Set (FreeGroup RotationGenerator)) r
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of i =>
      fin_cases i
      · change baseToRotation (rotationToBase X) = X
        simp
      · change baseToRotation (rotationToBase Y) = Y
        simp
      · change baseToRotation (rotationToBase Z) = Z
        simp
  | inv_of i hi => simpa only [map_inv] using congrArg Inv.inv hi
  | mul a b ha hb => simpa only [map_mul] using congrArg₂ (· * ·) ha hb

/-- Consequently the abstract eight-relator rotation presentation embeds in
the literal base. -/
theorem rotationToBase_injective : Function.Injective rotationToBase := by
  apply Function.LeftInverse.injective
  intro r
  exact DFunLike.congr_fun baseToRotation_comp_rotationToBase r

theorem baseToRotation_surjective : Function.Surjective baseToRotation := by
  intro r
  refine ⟨rotationToBase r, ?_⟩
  exact DFunLike.congr_fun baseToRotation_comp_rotationToBase r

/-- Killing translations really kills their whole generated subgroup. -/
theorem translations_le_baseToRotation_ker :
    translations ≤ baseToRotation.ker := by
  change Subgroup.closure ({v1, v2, v3} : Set Base) ≤ baseToRotation.ker
  rw [Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | rfl | rfl
  · exact baseToRotation_v1
  · exact baseToRotation_v2
  · exact baseToRotation_v3

/-- The range of the embedded rotation presentation is exactly the subgroup
generated by the three literal rotations. -/
theorem rotationToBase_range : rotationToBase.range = rotations := by
  apply le_antisymm
  · intro _ hr
    rcases hr with ⟨r, rfl⟩
    obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective
      (rotationRelators : Set (FreeGroup RotationGenerator)) r
    induction w using FreeGroup.induction_on with
    | C1 => simp
    | of i =>
        fin_cases i
        · exact x_mem_rotations
        · exact y_mem_rotations
        · exact z_mem_rotations
    | inv_of i hi => simpa only [map_inv] using rotations.inv_mem hi
    | mul a b ha hb => simpa only [map_mul] using rotations.mul_mem ha hb
  · change Subgroup.closure ({x, y, z} : Set Base) ≤ rotationToBase.range
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨X, rotationToBase_X⟩
    · exact ⟨Y, rotationToBase_Y⟩
    · exact ⟨Z, rotationToBase_Z⟩

/-- The kernel of the rotation retraction is exactly the translation
subgroup.  Thus the literal base is an internally split extension of its
three-generator rotation presentation by its translation subgroup. -/
theorem baseToRotation_ker_eq_translations :
    baseToRotation.ker = translations := by
  apply le_antisymm
  · intro g hg
    obtain ⟨a, ha, r, hr, harg⟩ := exists_translation_mul_rotation g
    have haKer : a ∈ baseToRotation.ker :=
      translations_le_baseToRotation_ker ha
    have hmapr : baseToRotation r = 1 := by
      have hproduct : baseToRotation a * baseToRotation r = 1 := by
        rw [← map_mul, harg]
        exact hg
      simpa only [MonoidHom.mem_ker.mp haKer, one_mul] using hproduct
    have hrange : r ∈ rotationToBase.range := by
      rw [rotationToBase_range]
      exact hr
    obtain ⟨q, hq⟩ := hrange
    have hleft := DFunLike.congr_fun baseToRotation_comp_rotationToBase q
    change baseToRotation (rotationToBase q) = q at hleft
    rw [hq, hmapr] at hleft
    have hrone : r = 1 := by rw [← hq, ← hleft]; simp
    rw [← harg, hrone, mul_one]
    exact ha
  · exact translations_le_baseToRotation_ker

theorem translations_inf_rotations : translations ⊓ rotations = ⊥ := by
  apply le_antisymm
  · intro g hg
    have hker : g ∈ baseToRotation.ker := by
      rw [baseToRotation_ker_eq_translations]
      exact hg.1
    have hrange : g ∈ rotationToBase.range := by
      rw [rotationToBase_range]
      exact hg.2
    obtain ⟨q, hq⟩ := hrange
    have hleft := DFunLike.congr_fun baseToRotation_comp_rotationToBase q
    change baseToRotation (rotationToBase q) = q at hleft
    rw [hq, MonoidHom.mem_ker.mp hker] at hleft
    rw [← hq, ← hleft]
    simp
  · exact bot_le

/-! ## Exact internal semidirect-product form -/

instance translations_normal : translations.Normal where
  conj_mem := by
    intro u hu g
    have hg : g ∈ Subgroup.normalizer translations := by
      rw [normalizer_translations_eq_top]
      exact Subgroup.mem_top g
    exact ((Subgroup.mem_normalizer_iff.mp hg) u).mp hu

/-- Each base element has a unique translation--rotation factorization. -/
theorem translations_isComplement_rotations :
    translations.IsComplement' rotations := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff_inf_le, translations_inf_rotations]
  · have hnorm : rotations ≤ Subgroup.normalizer (translations : Set Base) := by
      rw [normalizer_translations_eq_top]
      exact le_top
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left
      translations rotations hnorm]
    rw [translations_sup_rotations]
    rfl

/-- The literal base is exactly the internal semidirect product determined
by conjugation of translations by rotations. -/
noncomputable def internalSemidirectEquiv :
    translations ⋊[
      (translations.normalizerMonoidHom).comp
        (Subgroup.inclusion
          (translations.normalizer_eq_top ▸
            (show rotations ≤ (⊤ : Subgroup Base) from le_top)))] rotations ≃*
      Base :=
  SemidirectProduct.mulEquivSubgroup translations_isComplement_rotations

@[simp] theorem internalSemidirectEquiv_apply
    (g : translations ⋊[
      (translations.normalizerMonoidHom).comp
        (Subgroup.inclusion
          (translations.normalizer_eq_top ▸
            (show rotations ≤ (⊤ : Subgroup Base) from le_top)))] rotations) :
    internalSemidirectEquiv g = (g.left : Base) * (g.right : Base) :=
  rfl

/-- The abstract rotation presentation is multiplicatively equivalent to
the internal rotation subgroup. -/
noncomputable def rotationEquivRotations : Rotation ≃* rotations :=
  MulEquiv.ofBijective
    (rotationToBase.codRestrict rotations fun r => by
      rw [← rotationToBase_range]
      exact ⟨r, rfl⟩)
    ⟨fun _ _ h => rotationToBase_injective (congrArg Subtype.val h), by
      intro r
      have hr : (r : Base) ∈ rotationToBase.range := by
        rw [rotationToBase_range]
        exact r.property
      rcases hr with ⟨q, hq⟩
      exact ⟨q, Subtype.ext hq⟩⟩

@[simp] theorem rotationEquivRotations_X :
    (rotationEquivRotations X : Base) = LiteralBaseRelations.x := by
  change rotationToBase X = LiteralBaseRelations.x
  exact rotationToBase_X

@[simp] theorem rotationEquivRotations_Y :
    (rotationEquivRotations Y : Base) = LiteralBaseRelations.y := by
  change rotationToBase Y = LiteralBaseRelations.y
  exact rotationToBase_Y

@[simp] theorem rotationEquivRotations_Z :
    (rotationEquivRotations Z : Base) = LiteralBaseRelations.z := by
  change rotationToBase Z = LiteralBaseRelations.z
  exact rotationToBase_Z

end

end LiteralBaseRotationRetract
end GroupApproximation
