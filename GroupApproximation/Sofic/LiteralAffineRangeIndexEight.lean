import GroupApproximation.Monsters.AffineSL3Doubling
import GroupApproximation.Monsters.LiteralBaseCompleteness
import GroupApproximation.Sofic.LiteralBaseDoublingIndex
import GroupApproximation.Sofic.LiteralBaseRotationRetract
import GroupApproximation.Sofic.TargetEquivalence

/-!
# Exact index of the literal affine doubling range

The finite-index argument for the literal matrix carrier previously gave
only finiteness.  This file identifies its compressed range with the image of
the doubled subgroup in the complete six-generator affine presentation and
computes the latter index from the eight parity classes.
-/

namespace GroupApproximation
namespace LiteralAffineRangeIndexEight

open LiteralNonMFPresentation LiteralBaseRelations
open LiteralNonMFLinearWitness ExplicitLinearModel
open LiteralBaseAffineQuotient LiteralBaseCompleteness
open LiteralBaseTranslationNormal LiteralBaseTranslationLattice
open LiteralBaseRotationRetract LiteralBaseDoublingIndex

noncomputable section

abbrev Base := LiteralNonMFPresentation.Base
abbrev Lattice := LiteralBaseTranslationLattice.Lattice
abbrev latticeDouble : Multiplicative Lattice →* Multiplicative Lattice :=
  AffineSL3Doubling.doubleMul

/-! ## The compressed range is the transported doubled subgroup -/

/-- Doubling transported from the matrix carrier to the complete literal
presentation. -/
noncomputable def baseCompression : Base →* Base :=
  baseAffineEquiv.symm.toMonoidHom.comp
    (conjD.comp baseAffineEquiv.toMonoidHom)

@[simp] theorem baseAffineEquiv_baseCompression (g : Base) :
    baseAffineEquiv (baseCompression g) = conjD (baseAffineEquiv g) := by
  simp [baseCompression]

@[simp] theorem baseAffineEquiv_apply (g : Base) :
    baseAffineEquiv g = affineQuotient g := rfl

theorem baseCompression_v1 :
    baseCompression LiteralBaseRelations.v1 = LiteralBaseRelations.v1 ^ 2 := by
  apply baseAffineEquiv.injective
  rw [baseAffineEquiv_baseCompression, map_pow, baseAffineEquiv_apply,
    affineQuotient_v1, conjD_v1G]

theorem baseCompression_v2 :
    baseCompression LiteralBaseRelations.v2 = LiteralBaseRelations.v2 ^ 2 := by
  apply baseAffineEquiv.injective
  rw [baseAffineEquiv_baseCompression, map_pow, baseAffineEquiv_apply,
    affineQuotient_v2, conjD_v2G]

theorem baseCompression_v3 :
    baseCompression LiteralBaseRelations.v3 = LiteralBaseRelations.v3 ^ 2 := by
  apply baseAffineEquiv.injective
  rw [baseAffineEquiv_baseCompression, map_pow, baseAffineEquiv_apply,
    affineQuotient_v3, conjD_v3G]

theorem baseCompression_x :
    baseCompression LiteralBaseRelations.x = LiteralBaseRelations.x := by
  apply baseAffineEquiv.injective
  rw [baseAffineEquiv_baseCompression, baseAffineEquiv_apply,
    affineQuotient_x, conjD_xG]

theorem baseCompression_y :
    baseCompression LiteralBaseRelations.y = LiteralBaseRelations.y := by
  apply baseAffineEquiv.injective
  rw [baseAffineEquiv_baseCompression, baseAffineEquiv_apply,
    affineQuotient_y, conjD_yG]

theorem baseCompression_z :
    baseCompression LiteralBaseRelations.z = LiteralBaseRelations.z := by
  apply baseAffineEquiv.injective
  rw [baseAffineEquiv_baseCompression, baseAffineEquiv_apply,
    affineQuotient_z, conjD_zG]

theorem baseCompression_generator_mem (i : BaseGenerator) :
    baseCompression (PresentedGroup.of i) ∈ doubledBase := by
  fin_cases i
  · simpa [LiteralBaseRelations.v1, v1Index, baseCompression_v1] using
      v1sq_mem_doubledBase
  · simpa [LiteralBaseRelations.v2, v2Index, baseCompression_v2] using
      v2sq_mem_doubledBase
  · simpa [LiteralBaseRelations.v3, v3Index, baseCompression_v3] using
      v3sq_mem_doubledBase
  · simpa [LiteralBaseRelations.x, xIndex, baseCompression_x] using
      x_mem_doubledBase
  · simpa [LiteralBaseRelations.y, yIndex, baseCompression_y] using
      y_mem_doubledBase
  · simpa [LiteralBaseRelations.z, zIndex, baseCompression_z] using
      z_mem_doubledBase

theorem baseCompression_mem_doubledBase (g : Base) :
    baseCompression g ∈ doubledBase := by
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective _ g
  induction w using FreeGroup.induction_on with
  | C1 => rw [map_one, map_one]; exact doubledBase.one_mem
  | of i => simpa using baseCompression_generator_mem i
  | inv_of i hi => rw [map_inv, map_inv]; exact doubledBase.inv_mem hi
  | mul a b ha hb => rw [map_mul, map_mul]; exact doubledBase.mul_mem ha hb

/-- The matrix compressed range is exactly the image of the doubled subgroup
under the complete affine evaluation. -/
theorem map_doubledBase_eq_conjD_range :
    doubledBase.map affineQuotient = conjD.range := by
  apply le_antisymm map_doubledBase_le_conjD_range
  rintro g ⟨h, rfl⟩
  obtain ⟨b, rfl⟩ := affineQuotient_surjective h
  refine ⟨baseCompression b, baseCompression_mem_doubledBase b, ?_⟩
  exact baseAffineEquiv_baseCompression b

/-! ## Eight parity cosets -/

/-- The even translation subgroup inside the literal base. -/
def evenTranslations : Subgroup Base :=
  latticeDouble.range.map latticeToBase

theorem latticeToBase_double (a : Multiplicative Lattice) :
    latticeToBase (latticeDouble a) = latticeToBase a ^ 2 := by
  have hd : latticeDouble a = a * a := by
    apply Multiplicative.toAdd.injective
    change 2 • a.toAdd = a.toAdd + a.toAdd
    exact two_smul Lattice a.toAdd
  rw [hd, map_mul, pow_two]

theorem evenTranslations_le_translations : evenTranslations ≤ translations := by
  rintro g ⟨a, _ha, rfl⟩
  rw [← latticeToBase_range]
  exact ⟨a, rfl⟩

theorem translation_sq_mem_evenTranslations {g : Base}
    (hg : g ∈ translations) : g ^ 2 ∈ evenTranslations := by
  rw [← latticeToBase_range] at hg
  obtain ⟨a, rfl⟩ := hg
  refine ⟨latticeDouble a, ⟨a, rfl⟩, ?_⟩
  exact latticeToBase_double a

theorem rotation_conj_even_mem {r e : Base} (_hr : r ∈ rotations)
    (he : e ∈ evenTranslations) : r * e * r⁻¹ ∈ evenTranslations := by
  obtain ⟨a, ⟨b, rfl⟩, rfl⟩ := he
  rw [latticeToBase_double]
  have hrnorm : r ∈ Subgroup.normalizer translations := by
    rw [normalizer_translations_eq_top]
    exact Subgroup.mem_top r
  have hu : r * latticeToBase b * r⁻¹ ∈ translations :=
    (Subgroup.mem_normalizer_iff.mp hrnorm (latticeToBase b)).mp
      (by rw [← latticeToBase_range]; exact ⟨b, rfl⟩)
  have heq : r * latticeToBase b ^ 2 * r⁻¹ =
      (r * latticeToBase b * r⁻¹) ^ 2 := by
    simp only [pow_two]
    group
  rw [heq]
  exact translation_sq_mem_evenTranslations hu

/-- Elements with even translation coordinate and arbitrary rotation. -/
def evenRotation : Subgroup Base where
  carrier := {g | ∃ e ∈ evenTranslations, ∃ r ∈ rotations, g = e * r}
  one_mem' := ⟨1, evenTranslations.one_mem, 1, rotations.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨e, he, r, hr, rfl⟩ ⟨f, hf, s, hs, rfl⟩
    refine ⟨e * (r * f * r⁻¹), evenTranslations.mul_mem he
      (rotation_conj_even_mem hr hf), r * s, rotations.mul_mem hr hs, ?_⟩
    group
  inv_mem' := by
    rintro a ⟨e, he, r, hr, rfl⟩
    refine ⟨r⁻¹ * e⁻¹ * r, ?_, r⁻¹, rotations.inv_mem hr, ?_⟩
    · simpa only [inv_inv] using
        rotation_conj_even_mem (rotations.inv_mem hr)
          (evenTranslations.inv_mem he)
    group

theorem evenTranslations_le_doubledBase : evenTranslations ≤ doubledBase := by
  rintro g ⟨a, ⟨b, rfl⟩, rfl⟩
  convert latticeToBase_even_mem b.toAdd using 1
  apply congrArg latticeToBase
  apply Multiplicative.toAdd.injective
  change 2 • b.toAdd = fun i ↦ 2 * b.toAdd i
  funext i
  simp [Pi.smul_apply]

theorem doubledBase_eq_evenRotation : doubledBase = evenRotation := by
  apply le_antisymm
  · rw [doubledBase, Subgroup.closure_le]
    intro g hg
    rcases hg with h | h | h | h | h | h
    · subst h; exact ⟨1, evenTranslations.one_mem, LiteralBaseRelations.x,
        x_mem_rotations, by simp⟩
    · subst h; exact ⟨1, evenTranslations.one_mem, LiteralBaseRelations.y,
        y_mem_rotations, by simp⟩
    · subst h; exact ⟨1, evenTranslations.one_mem, LiteralBaseRelations.z,
        z_mem_rotations, by simp⟩
    · subst h; exact ⟨LiteralBaseRelations.v1 ^ 2,
        translation_sq_mem_evenTranslations v1_mem_translations,
        1, rotations.one_mem, by simp⟩
    · subst h; exact ⟨LiteralBaseRelations.v2 ^ 2,
        translation_sq_mem_evenTranslations v2_mem_translations,
        1, rotations.one_mem, by simp⟩
    · rw [Set.mem_singleton_iff] at h
      subst h; exact ⟨LiteralBaseRelations.v3 ^ 2,
        translation_sq_mem_evenTranslations v3_mem_translations,
        1, rotations.one_mem, by simp⟩
  · rintro g ⟨e, he, r, hr, rfl⟩
    exact doubledBase.mul_mem (evenTranslations_le_doubledBase he)
      (rotations_le_doubledBase hr)

/-- A pure translation lying in the even-rotation subgroup is even. -/
theorem translation_mem_evenTranslations_of_mem_evenRotation {t : Base}
    (ht : t ∈ translations) (hE : t ∈ evenRotation) :
    t ∈ evenTranslations := by
  obtain ⟨e, he, r, hr, htr⟩ := hE
  have heT : e ∈ translations := evenTranslations_le_translations he
  have hrT : r ∈ translations := by
    have hre : r = e⁻¹ * t := by rw [htr]; group
    rw [hre]
    exact translations.mul_mem (translations.inv_mem heT) ht
  have hrbot : r ∈ (⊥ : Subgroup Base) := by
    rw [← translations_inf_rotations]
    exact ⟨hrT, hr⟩
  have hrone : r = 1 := Subgroup.mem_bot.mp hrbot
  rw [hrone, mul_one] at htr
  rwa [htr]

abbrev DoubleCosets :=
  Multiplicative Lattice ⧸ latticeDouble.range

abbrev DoubledBaseCosets := Base ⧸ doubledBase

/-- Inclusion of the translation lattice induces the parity-coset map. -/
def parityCosetMap : DoubleCosets → DoubledBaseCosets :=
  Quotient.map' latticeToBase (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [← map_inv, ← map_mul]
    exact evenTranslations_le_doubledBase ⟨a⁻¹ * b, hab, rfl⟩)

theorem parityCosetMap_surjective : Function.Surjective parityCosetMap := by
  refine Quotient.ind' (fun g ↦ ?_)
  obtain ⟨t, ht, r, hr, rfl⟩ := exists_translation_mul_rotation g
  rw [← latticeToBase_range] at ht
  obtain ⟨a, rfl⟩ := ht
  refine ⟨QuotientGroup.mk a, ?_⟩
  rw [parityCosetMap, Quotient.map'_mk'']
  apply Quotient.sound'
  apply QuotientGroup.leftRel_apply.mpr
  simpa using rotations_le_doubledBase hr

theorem parityCosetMap_injective : Function.Injective parityCosetMap := by
  refine Quotient.ind' (fun a ↦ Quotient.ind' (fun b hab ↦ ?_))
  apply Quotient.sound'
  apply QuotientGroup.leftRel_apply.mpr
  have htarget : QuotientGroup.leftRel doubledBase
      (latticeToBase a) (latticeToBase b) := Quotient.exact' hab
  rw [QuotientGroup.leftRel_apply, ← map_inv, ← map_mul] at htarget
  have htrans : latticeToBase (a⁻¹ * b) ∈ translations := by
    rw [← latticeToBase_range]
    exact ⟨a⁻¹ * b, rfl⟩
  have heven : latticeToBase (a⁻¹ * b) ∈ evenTranslations :=
    translation_mem_evenTranslations_of_mem_evenRotation htrans
      (doubledBase_eq_evenRotation ▸ htarget)
  obtain ⟨d, hd, hdeq⟩ := heven
  have habd : a⁻¹ * b = d :=
    latticeToBase_injective (hdeq.symm)
  rwa [habd]

/-- Parity classes are exactly the cosets of the doubled subgroup. -/
noncomputable def parityCosetEquiv : DoubleCosets ≃ DoubledBaseCosets :=
  Equiv.ofBijective parityCosetMap
    ⟨parityCosetMap_injective, parityCosetMap_surjective⟩

/-- The doubled subgroup in the complete literal base has index eight. -/
theorem doubledBase_index_eq_eight : doubledBase.index = 8 := by
  rw [Subgroup.index_eq_card, ← Nat.card_congr parityCosetEquiv,
    ← Subgroup.index_eq_card]
  exact AffineSL3Doubling.doubleMul_range_index

/-- The compressed range in the literal affine matrix carrier has index
exactly eight. -/
theorem conjD_range_index_eq_eight : conjD.range.index = 8 := by
  rw [← map_doubledBase_eq_conjD_range,
    index_map_eq_index_of_ker_le affineQuotient affineQuotient_surjective
      (MonoidHom.ker_eq_bot affineQuotient affineQuotient_injective ▸ bot_le)]
  exact doubledBase_index_eq_eight

end

end LiteralAffineRangeIndexEight
end GroupApproximation
