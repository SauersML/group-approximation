import GroupApproximation.Monsters.P13DescentMaster
import GroupApproximation.Sofic.LiteralBaseP13RotationQuotient
import GroupApproximation.Sofic.LiteralBaseAffineQuotient
import GroupApproximation.Sofic.LiteralBaseTranslationNormal

/-!
# Completeness of the literal base presentation

The canonical evaluation of the twenty-relator literal base presentation in
the affine rational matrix group is an isomorphism onto its image:
`Base ≃* gammaBar`.  Classically this is the statement that the twenty
relators present `ℤ³ ⋊ SL₃(ℤ)`.

The proof assembles four finished layers.  The semidirect skeleton of the
presented base (`LiteralBaseTranslationNormal`,
`LiteralBaseRotationRetract`) reduces injectivity to the two factors.  On
the rotation factor, the eight-relator group receives the thirteen-relator
Steinberg presentation by audited short words
(`LiteralBaseP13RotationQuotient`), surjectively; the completeness theorem
`P13DescentMaster.toSL3_injective` then forces the rotation matrix model
to be injective.  On the translation factor, the three commuting
generators normal-form into `v₁^a v₂^b v₃^c`, and the affine matrices
read off the exponents.
-/

namespace GroupApproximation
namespace LiteralBaseCompleteness

open PresentedGroupRelatorReplay LiteralBaseP13RotationReplay
open LiteralBaseRotationRetract LiteralBaseP13RotationQuotient
open LiteralBaseTranslationNormal LiteralBaseRelations
open LiteralBaseAffineQuotient LiteralNonMFLinearWitness
open ExplicitLinearModel LiteralP13Presentation LiteralP13MatrixModel
open Matrix

noncomputable section

private abbrev Base := LiteralNonMFPresentation.Base

/-! ## Torsion of the rotation units -/

private theorem xM_cube : xM * xM * xM = 1 := xM_orderThree'

private theorem yM_cube : yM * yM * yM = 1 := yM_orderThree'

private theorem xU_cube : xU ^ 3 = 1 := by
  ext
  rw [Units.val_pow_eq_pow_val, pow_succ, pow_succ, pow_one]
  exact xM_cube

private theorem yU_cube : yU ^ 3 = 1 := by
  ext
  rw [Units.val_pow_eq_pow_val, pow_succ, pow_succ, pow_one]
  exact yM_cube

private theorem zU_sq : zU ^ 2 = 1 := by
  ext
  rw [Units.val_pow_eq_pow_val, pow_two]
  exact zM_orderTwo

private theorem xU_inv : xU⁻¹ = xU * xU := by
  apply inv_eq_of_mul_eq_one_left
  have h := xU_cube
  rw [pow_succ, pow_two] at h
  exact h

private theorem yU_inv : yU⁻¹ = yU * yU := by
  apply inv_eq_of_mul_eq_one_left
  have h := yU_cube
  rw [pow_succ, pow_two] at h
  exact h

private theorem zU_inv : zU⁻¹ = zU := by
  apply inv_eq_of_mul_eq_one_left
  have h := zU_sq
  rw [pow_two] at h
  exact h

/-! ## The rotation matrix model -/

private def rotUnit : RotationGenerator → Matˣ
  | 0 => xU
  | 1 => yU
  | 2 => zU

private macro "verify_unit_matrix" : tactic =>
  `(tactic|
    (ext : 1
     simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one]
     exact Matrix.ext fun i j => by
       fin_cases i <;> fin_cases j <;>
         norm_num [Matrix.mul_apply, Matrix.one_apply, pow_succ,
           Fin.sum_univ_succ, xM, yM, zM]))

private theorem rotUnit_kills :
    ∀ r ∈ (rotationRelators : Set (FreeGroup RotationGenerator)),
      FreeGroup.lift rotUnit r = 1 := by
  intro r hr
  rw [Finset.mem_coe, mem_rotationRelators_iff] at hr
  obtain ⟨i, rfl⟩ := hr
  fin_cases i
  · show FreeGroup.lift rotUnit relXCube = 1
    simpa only [relXCube, map_pow, FreeGroup.lift.of] using xU_cube
  · show FreeGroup.lift rotUnit relYCube = 1
    simpa only [relYCube, map_pow, FreeGroup.lift.of] using yU_cube
  · show FreeGroup.lift rotUnit relZSq = 1
    simpa only [relZSq, map_pow, FreeGroup.lift.of] using zU_sq
  · show FreeGroup.lift rotUnit relXZCube = 1
    simp only [relXZCube, map_pow, map_mul, FreeGroup.lift.of]
    show ((xU * zU) ^ 3 : Matˣ) = 1
    verify_unit_matrix
  · show FreeGroup.lift rotUnit relYZCube = 1
    simp only [relYZCube, map_pow, map_mul, FreeGroup.lift.of]
    show ((yU * zU) ^ 3 : Matˣ) = 1
    verify_unit_matrix
  · show FreeGroup.lift rotUnit relXInvZXY = 1
    simp only [relXInvZXY, map_pow, map_mul, map_inv, FreeGroup.lift.of]
    show ((xU⁻¹ * zU * xU * yU) ^ 2 : Matˣ) = 1
    rw [xU_inv]
    verify_unit_matrix
  · show FreeGroup.lift rotUnit relYInvZYX = 1
    simp only [relYInvZYX, map_pow, map_mul, map_inv, FreeGroup.lift.of]
    show ((yU⁻¹ * zU * yU * xU) ^ 2 : Matˣ) = 1
    rw [yU_inv]
    verify_unit_matrix
  · show FreeGroup.lift rotUnit relXYSix = 1
    simp only [relXYSix, map_pow, map_mul, FreeGroup.lift.of]
    show ((xU * yU) ^ 6 : Matˣ) = 1
    verify_unit_matrix

/-- The matrix model of the abstract eight-relator rotation group. -/
def rotationToMat : Rotation →* Matˣ :=
  PresentedGroup.toGroup rotUnit_kills

@[simp] theorem rotationToMat_X : rotationToMat X = xU :=
  PresentedGroup.toGroup.of rotUnit_kills

@[simp] theorem rotationToMat_Y : rotationToMat Y = yU :=
  PresentedGroup.toGroup.of rotUnit_kills

@[simp] theorem rotationToMat_Z : rotationToMat Z = zU :=
  PresentedGroup.toGroup.of rotUnit_kills

private theorem rotationToMat_word (w : FreeGroup RotationGenerator) :
    rotationToMat (rotationWord w) = FreeGroup.lift rotUnit w := by
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of i =>
      rw [rotationWord_of]
      fin_cases i
      · simpa using rotationToMat_X
      · simpa using rotationToMat_Y
      · simpa using rotationToMat_Z
  | inv_of i h => simpa only [map_inv] using congrArg Inv.inv h
  | mul a b ha hb => simpa only [map_mul] using congrArg₂ (· * ·) ha hb

/-! ## The block embedding of `SL₃(ℤ)` -/

private def blockMonoid : Matrix (Fin 3) (Fin 3) ℚ →* Mat where
  toFun A :=
    (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 1) (Fin 1) ℚ)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm
  map_one' := by
    rw [Matrix.fromBlocks_one]
    exact Matrix.submatrix_one_equiv finSumFinEquiv.symm
  map_mul' A B := by
    rw [← Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv _,
      Matrix.fromBlocks_multiply]
    simp

/-- The `4 × 4` affine block embedding of the integral special linear
group. -/
def blockEmbed4 : SL3 →* Matˣ :=
  (Units.map blockMonoid).comp
    ((Units.map ((Int.castRingHom ℚ).mapMatrix.toMonoidHom)).comp
      Matrix.SpecialLinearGroup.toGL)

private theorem blockEmbed4_val (A : SL3) :
    (blockEmbed4 A).val =
      (Matrix.fromBlocks ((A : Matrix (Fin 3) (Fin 3) ℤ).map
        (Int.cast : ℤ → ℚ)) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℚ)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := rfl

/-- Explicit entries of the block embedding. -/
private theorem blockEmbed4_val_explicit (A : SL3) :
    (blockEmbed4 A).val =
      !![((A : Matrix (Fin 3) (Fin 3) ℤ) 0 0 : ℚ),
          ((A : Matrix (Fin 3) (Fin 3) ℤ) 0 1 : ℚ),
          ((A : Matrix (Fin 3) (Fin 3) ℤ) 0 2 : ℚ), 0;
        ((A : Matrix (Fin 3) (Fin 3) ℤ) 1 0 : ℚ),
          ((A : Matrix (Fin 3) (Fin 3) ℤ) 1 1 : ℚ),
          ((A : Matrix (Fin 3) (Fin 3) ℤ) 1 2 : ℚ), 0;
        ((A : Matrix (Fin 3) (Fin 3) ℤ) 2 0 : ℚ),
          ((A : Matrix (Fin 3) (Fin 3) ℤ) 2 1 : ℚ),
          ((A : Matrix (Fin 3) (Fin 3) ℤ) 2 2 : ℚ), 0;
        0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | simp [blockEmbed4_val, Matrix.submatrix_apply, Matrix.fromBlocks,
          finSumFinEquiv, Fin.addCases, Matrix.map_apply]

private theorem blockEmbed4_eq_one {A : SL3} (h : blockEmbed4 A = 1) :
    A = 1 := by
  have hval := congrArg Units.val h
  rw [blockEmbed4_val_explicit] at hval
  ext i j
  have hone : ∀ i' j' : Fin 4, (1 : Mat) i' j' = if i' = j' then 1 else 0 :=
    fun i' j' => Matrix.one_apply
  fin_cases i <;> fin_cases j <;>
    · have := congrFun (congrFun hval (by exact ⟨_, by norm_num⟩ : Fin 4))
        (⟨_, by norm_num⟩ : Fin 4)
      exact_mod_cast (by simpa [Matrix.one_apply] using this)

/-! ## The compatibility square -/

/-- The affine evaluation of the embedded rotation subgroup agrees with the
rotation matrix model. -/
private theorem affineQuotient_rotationToBase (r : Rotation) :
    ((affineQuotient (rotationToBase r) : gammaBar) : Matˣ) =
      rotationToMat r := by
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective
    (rotationRelators : Set (FreeGroup RotationGenerator)) r
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of i =>
      fin_cases i
      · show ((affineQuotient (rotationToBase X) : gammaBar) : Matˣ) =
          rotationToMat X
        rw [rotationToBase_X, rotationToMat_X]
        rfl
      · show ((affineQuotient (rotationToBase Y) : gammaBar) : Matˣ) =
          rotationToMat Y
        rw [rotationToBase_Y, rotationToMat_Y]
        rfl
      · show ((affineQuotient (rotationToBase Z) : gammaBar) : Matˣ) =
          rotationToMat Z
        rw [rotationToBase_Z, rotationToMat_Z]
        rfl
  | inv_of i h => simpa only [map_inv] using congrArg Inv.inv h
  | mul a b ha hb => simpa only [map_mul] using congrArg₂ (· * ·) ha hb

private macro "verify_word_matrix" : tactic =>
  `(tactic|
    (refine Units.ext ?_
     simp only [Units.val_mul, Units.val_one]
     rw [blockEmbed4_val_explicit]
     exact Matrix.ext fun i j => by
       fin_cases i <;> fin_cases j <;>
         norm_num [Matrix.mul_apply, Fin.sum_univ_succ, elem,
           xM, yM, zM]))

/-- The Steinberg letters evaluate through the rotation words to the block
elementary matrices. -/
private theorem rotationToMat_p13 (i : P13Generator) :
    rotationToMat (p13ToRotation (PresentedGroup.of i)) =
      blockEmbed4 (elem i) := by
  fin_cases i
  · rw [show (PresentedGroup.of (0 : Fin 6) : P13) = E12 from rfl,
      p13ToRotation_E12_word, rotationToMat_word]
    show FreeGroup.lift rotUnit (FreeGroup.mk
      [((1 : Fin 3), false), (0, true), (2, true), (1, false), (0, false)]) =
      blockEmbed4 (elem 0)
    rw [FreeGroup.lift_mk]
    show yU⁻¹ * (xU * (zU * (yU⁻¹ * (xU⁻¹ * 1)))) = blockEmbed4 (elem 0)
    rw [yU_inv, xU_inv, mul_one]
    verify_word_matrix
  · rw [show (PresentedGroup.of (1 : Fin 6) : P13) = E13 from rfl,
      p13ToRotation_E13_word, rotationToMat_word]
    show FreeGroup.lift rotUnit (FreeGroup.mk
      [((0 : Fin 3), true), (2, true), (1, false), (0, false), (1, true)]) =
      blockEmbed4 (elem 1)
    rw [FreeGroup.lift_mk]
    show xU * (zU * (yU⁻¹ * (xU⁻¹ * (yU * 1)))) = blockEmbed4 (elem 1)
    rw [yU_inv, xU_inv, mul_one]
    verify_word_matrix
  · rw [show (PresentedGroup.of (2 : Fin 6) : P13) = E21 from rfl,
      p13ToRotation_E21_word, rotationToMat_word]
    show FreeGroup.lift rotUnit (FreeGroup.mk
      [((1 : Fin 3), false), (0, true), (1, true), (0, true), (2, true)]) =
      blockEmbed4 (elem 2)
    rw [FreeGroup.lift_mk]
    show yU⁻¹ * (xU * (yU * (xU * (zU * 1)))) = blockEmbed4 (elem 2)
    rw [yU_inv, mul_one]
    verify_word_matrix
  · rw [show (PresentedGroup.of (3 : Fin 6) : P13) = E23 from rfl,
      p13ToRotation_E23_word, rotationToMat_word]
    show FreeGroup.lift rotUnit (FreeGroup.mk
      [((0 : Fin 3), false), (1, false), (0, true), (2, true), (1, false)]) =
      blockEmbed4 (elem 3)
    rw [FreeGroup.lift_mk]
    show xU⁻¹ * (yU⁻¹ * (xU * (zU * (yU⁻¹ * 1)))) = blockEmbed4 (elem 3)
    rw [yU_inv, xU_inv, mul_one]
    verify_word_matrix
  · rw [show (PresentedGroup.of (4 : Fin 6) : P13) = E31 from rfl,
      p13ToRotation_E31_word, rotationToMat_word]
    show FreeGroup.lift rotUnit (FreeGroup.mk
      [((0 : Fin 3), true), (1, false), (0, true), (2, true), (1, false),
        (0, true)]) = blockEmbed4 (elem 4)
    rw [FreeGroup.lift_mk]
    show xU * (yU⁻¹ * (xU * (zU * (yU⁻¹ * (xU * 1))))) =
      blockEmbed4 (elem 4)
    rw [yU_inv, mul_one]
    verify_word_matrix
  · rw [show (PresentedGroup.of (5 : Fin 6) : P13) = E32 from rfl,
      p13ToRotation_E32_word, rotationToMat_word]
    show FreeGroup.lift rotUnit (FreeGroup.mk
      [((0 : Fin 3), false), (2, true), (1, false), (0, false), (1, true),
        (0, false)]) = blockEmbed4 (elem 5)
    rw [FreeGroup.lift_mk]
    show xU⁻¹ * (zU * (yU⁻¹ * (xU⁻¹ * (yU * (xU⁻¹ * 1))))) =
      blockEmbed4 (elem 5)
    rw [yU_inv, xU_inv, mul_one]
    verify_word_matrix

/-- The full compatibility square, as an equality of homomorphisms out of
the Steinberg presentation. -/
private theorem rotationToMat_comp_p13ToRotation :
    rotationToMat.comp p13ToRotation = blockEmbed4.comp toSL3 := by
  apply MonoidHom.ext
  intro p
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective
    (p13Relators : Set (FreeGroup P13Generator)) p
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of i =>
      show rotationToMat (p13ToRotation (PresentedGroup.of i)) =
        blockEmbed4 (toSL3 (PresentedGroup.of i))
      rw [toSL3_of, rotationToMat_p13]
  | inv_of i h => simpa only [map_inv] using congrArg Inv.inv h
  | mul a b ha hb => simpa only [map_mul] using congrArg₂ (· * ·) ha hb

/-- **Rotation injectivity.**  The eight-relator rotation presentation
injects into the matrices, by presentation completeness of the Steinberg
model. -/
theorem rotationToMat_injective : Function.Injective rotationToMat := by
  rw [injective_iff_map_eq_one]
  intro r hr
  obtain ⟨p, rfl⟩ := p13ToRotation_surjective r
  have h2 : blockEmbed4 (toSL3 p) = 1 := by
    have := DFunLike.congr_fun rotationToMat_comp_p13ToRotation p
    simp only [MonoidHom.comp_apply] at this
    rw [← this]
    exact hr
  have h3 : toSL3 p = 1 := blockEmbed4_eq_one h2
  have h4 : p = 1 :=
    (injective_iff_map_eq_one toSL3).mp P13DescentMaster.toSL3_injective p h3
  rw [h4, map_one]

/-! ## The translation normal form -/

private theorem exists_translation_form {τ : Base}
    (hτ : τ ∈ translations) :
    ∃ a b c : ℤ, τ = v1 ^ a * v2 ^ b * v3 ^ c := by
  have h12 : Commute (v1 : Base) v2 := by
    have := v1_commutes_translations v2_mem_translations
    exact this
  have h13 : Commute (v1 : Base) v3 := by
    have := v1_commutes_translations v3_mem_translations
    exact this
  have h23 : Commute (v2 : Base) v3 := by
    have := v2_commutes_translations v3_mem_translations
    exact this
  induction hτ using Subgroup.closure_induction with
  | mem u hu =>
      rcases hu with rfl | rfl | rfl
      · exact ⟨1, 0, 0, by simp⟩
      · exact ⟨0, 1, 0, by simp⟩
      · exact ⟨0, 0, 1, by simp⟩
  | one => exact ⟨0, 0, 0, by simp⟩
  | mul s t _ _ hs ht =>
      obtain ⟨a, b, c, rfl⟩ := hs
      obtain ⟨a', b', c', rfl⟩ := ht
      refine ⟨a + a', b + b', c + c', ?_⟩
      rw [zpow_add, zpow_add, zpow_add]
      have hc1 : Commute ((v2 : Base) ^ b * v3 ^ c) (v1 ^ a') :=
        Commute.mul_left (h12.symm.zpow_zpow b a')
          (h13.symm.zpow_zpow c a')
      have hc2 : Commute (v3 ^ c) (v2 ^ b') := h23.symm.zpow_zpow c b'
      calc v1 ^ a * v2 ^ b * v3 ^ c * (v1 ^ a' * v2 ^ b' * v3 ^ c')
          = v1 ^ a * ((v2 ^ b * v3 ^ c) * v1 ^ a') *
              (v2 ^ b' * v3 ^ c') := by group
        _ = v1 ^ a * (v1 ^ a' * (v2 ^ b * v3 ^ c)) *
              (v2 ^ b' * v3 ^ c') := by rw [hc1.eq]
        _ = (v1 ^ a * v1 ^ a') * (v2 ^ b * ((v3 ^ c) * v2 ^ b')) *
              v3 ^ c' := by group
        _ = (v1 ^ a * v1 ^ a') * (v2 ^ b * (v2 ^ b' * v3 ^ c)) *
              v3 ^ c' := by rw [hc2.eq]
        _ = v1 ^ a * v1 ^ a' * (v2 ^ b * v2 ^ b') *
              (v3 ^ c * v3 ^ c') := by group
  | inv s _ hs =>
      obtain ⟨a, b, c, rfl⟩ := hs
      refine ⟨-a, -b, -c, ?_⟩
      have i12 : ((v2 : Base) ^ b)⁻¹ * ((v1 : Base) ^ a)⁻¹ =
          ((v1 : Base) ^ a)⁻¹ * ((v2 : Base) ^ b)⁻¹ :=
        ((h12.zpow_zpow a b).inv_inv.symm).eq
      have i13 : ((v3 : Base) ^ c)⁻¹ * ((v1 : Base) ^ a)⁻¹ =
          ((v1 : Base) ^ a)⁻¹ * ((v3 : Base) ^ c)⁻¹ :=
        ((h13.zpow_zpow a c).inv_inv.symm).eq
      have i23 : ((v3 : Base) ^ c)⁻¹ * ((v2 : Base) ^ b)⁻¹ =
          ((v2 : Base) ^ b)⁻¹ * ((v3 : Base) ^ c)⁻¹ :=
        ((h23.zpow_zpow b c).inv_inv.symm).eq
      rw [zpow_neg, zpow_neg, zpow_neg]
      calc (v1 ^ a * v2 ^ b * v3 ^ c)⁻¹
          = (v3 ^ c)⁻¹ * (v2 ^ b)⁻¹ * (v1 ^ a)⁻¹ := by
            rw [mul_inv_rev, mul_inv_rev]; group
        _ = (v2 ^ b)⁻¹ * (v3 ^ c)⁻¹ * (v1 ^ a)⁻¹ := by rw [i23]
        _ = (v2 ^ b)⁻¹ * ((v3 ^ c)⁻¹ * (v1 ^ a)⁻¹) := by group
        _ = (v2 ^ b)⁻¹ * ((v1 ^ a)⁻¹ * (v3 ^ c)⁻¹) := by rw [i13]
        _ = (v2 ^ b)⁻¹ * (v1 ^ a)⁻¹ * (v3 ^ c)⁻¹ := by group
        _ = (v1 ^ a)⁻¹ * (v2 ^ b)⁻¹ * (v3 ^ c)⁻¹ := by rw [i12]

/-! ## Exponent extraction from the affine matrices -/

private theorem v1U_zpow (a : ℤ) :
    ((v1U ^ a : Matˣ) : Mat) = !![1,0,0,(a : ℚ); 0,1,0,0; 0,0,1,0; 0,0,0,1] := by
  induction a using Int.induction_on with
  | hz =>
      rw [zpow_zero]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
  | hp n ih =>
      rw [zpow_add_one, Units.val_mul, ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        (norm_num [Matrix.mul_apply, Fin.sum_univ_succ, v1M] <;>
          push_cast <;> ring)
  | hn n ih =>
      rw [zpow_sub_one, Units.val_mul, ih]
      have hinv : ((v1U⁻¹ : Matˣ) : Mat) = v1InvM := rfl
      rw [hinv]
      ext i j
      fin_cases i <;> fin_cases j <;>
        (norm_num [Matrix.mul_apply, Fin.sum_univ_succ, v1InvM] <;>
          push_cast <;> ring)

private theorem v2U_zpow (b : ℤ) :
    ((v2U ^ b : Matˣ) : Mat) = !![1,0,0,0; 0,1,0,(b : ℚ); 0,0,1,0; 0,0,0,1] := by
  induction b using Int.induction_on with
  | hz =>
      rw [zpow_zero]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
  | hp n ih =>
      rw [zpow_add_one, Units.val_mul, ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        (norm_num [Matrix.mul_apply, Fin.sum_univ_succ, v2M] <;>
          push_cast <;> ring)
  | hn n ih =>
      rw [zpow_sub_one, Units.val_mul, ih]
      have hinv : ((v2U⁻¹ : Matˣ) : Mat) = v2InvM := rfl
      rw [hinv]
      ext i j
      fin_cases i <;> fin_cases j <;>
        (norm_num [Matrix.mul_apply, Fin.sum_univ_succ, v2InvM] <;>
          push_cast <;> ring)

private theorem v3U_zpow (c : ℤ) :
    ((v3U ^ c : Matˣ) : Mat) = !![1,0,0,0; 0,1,0,0; 0,0,1,(c : ℚ); 0,0,0,1] := by
  induction c using Int.induction_on with
  | hz =>
      rw [zpow_zero]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
  | hp n ih =>
      rw [zpow_add_one, Units.val_mul, ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        (norm_num [Matrix.mul_apply, Fin.sum_univ_succ, v3M] <;>
          push_cast <;> ring)
  | hn n ih =>
      rw [zpow_sub_one, Units.val_mul, ih]
      have hinv : ((v3U⁻¹ : Matˣ) : Mat) = v3InvM := rfl
      rw [hinv]
      ext i j
      fin_cases i <;> fin_cases j <;>
        (norm_num [Matrix.mul_apply, Fin.sum_univ_succ, v3InvM] <;>
          push_cast <;> ring)

/-! ## Injectivity -/

/-- **Completeness of the twenty-relator base presentation.**  The affine
evaluation is injective; classically, the literal base presents
`ℤ³ ⋊ SL₃(ℤ)`. -/
theorem affineQuotient_injective : Function.Injective affineQuotient := by
  rw [injective_iff_map_eq_one]
  intro g hg
  set ρ : Base := rotationToBase (baseToRotation g) with hρdef
  have hτmem : g * ρ⁻¹ ∈ translations := by
    rw [← baseToRotation_ker_eq_translations, MonoidHom.mem_ker, map_mul,
      map_inv, hρdef]
    have hσ : baseToRotation (rotationToBase (baseToRotation g)) =
        baseToRotation g :=
      DFunLike.congr_fun baseToRotation_comp_rotationToBase
        (baseToRotation g)
    rw [hσ, mul_inv_cancel]
  obtain ⟨a, b, c, habc⟩ := exists_translation_form hτmem
  obtain ⟨p, hp⟩ := p13ToRotation_surjective (baseToRotation g)
  have hgdecomp : g = (g * ρ⁻¹) * ρ := by group
  have hval : ((affineQuotient g : gammaBar) : Matˣ) = 1 := by
    rw [hg]; rfl
  have hρval : ((affineQuotient ρ : gammaBar) : Matˣ) =
      blockEmbed4 (toSL3 p) := by
    rw [hρdef, ← hp, affineQuotient_rotationToBase]
    have := DFunLike.congr_fun rotationToMat_comp_p13ToRotation p
    simpa only [MonoidHom.comp_apply] using this
  have hτval : ((affineQuotient (g * ρ⁻¹) : gammaBar) : Matˣ) =
      v1U ^ a * v2U ^ b * v3U ^ c := by
    rw [habc]
    have h1 : affineQuotient (v1 : Base) = v1G := by
      show affineQuotient (PresentedGroup.of v1Index) = v1G
      rw [affineQuotient_generator, matrixBaseGenerator_v1]
    have h2 : affineQuotient (v2 : Base) = v2G := by
      show affineQuotient (PresentedGroup.of v2Index) = v2G
      rw [affineQuotient_generator, matrixBaseGenerator_v2]
    have h3 : affineQuotient (v3 : Base) = v3G := by
      show affineQuotient (PresentedGroup.of v3Index) = v3G
      rw [affineQuotient_generator, matrixBaseGenerator_v3]
    push_cast [map_mul, map_zpow, h1, h2, h3]
    rfl
  have hprod : (v1U ^ a * v2U ^ b * v3U ^ c) * blockEmbed4 (toSL3 p) =
      1 := by
    have := congrArg (fun u : gammaBar => (u : Matˣ))
      (show affineQuotient (g * ρ⁻¹) * affineQuotient ρ = 1 by
        rw [← map_mul, ← hgdecomp, hg])
    simpa only [Subgroup.coe_mul, Subgroup.coe_one, hτval, hρval]
      using this
  -- read off the matrix entries
  have hmat : (((v1U ^ a * v2U ^ b * v3U ^ c) *
      blockEmbed4 (toSL3 p) : Matˣ) : Mat) = 1 := by
    rw [hprod]; rfl
  rw [Units.val_mul, Units.val_mul, Units.val_mul, v1U_zpow, v2U_zpow,
    v3U_zpow, blockEmbed4_val_explicit] at hmat
  -- the linear corner forces the rotation part to be trivial
  have hcorner : toSL3 p = 1 := by
    ext i j
    have hent := congrFun (congrFun hmat
      (Fin.castLE (by norm_num) i)) (Fin.castLE (by norm_num) j)
    fin_cases i <;> fin_cases j <;>
      (simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero,
         Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero,
         Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
         Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
         Matrix.cons_val_fin_one, Matrix.head_fin_const,
         Matrix.one_apply, Fin.castLE] at hent <;>
       norm_num at hent ⊢ <;>
       exact_mod_cast hent)
  have hp1 : p = 1 :=
    (injective_iff_map_eq_one toSL3).mp P13DescentMaster.toSL3_injective
      p hcorner
  have hρ1 : ρ = 1 := by
    rw [hρdef, ← hp, hp1, map_one, map_one]
  -- the translation column forces the exponents to vanish
  rw [hcorner] at hmat
  have habc0 : a = 0 ∧ b = 0 ∧ c = 0 := by
    refine ⟨?_, ?_, ?_⟩
    · have hent := congrFun (congrFun hmat 0) 3
      simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero,
        Matrix.one_apply] at hent
      norm_num at hent
      exact_mod_cast hent
    · have hent := congrFun (congrFun hmat 1) 3
      simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero,
        Matrix.one_apply] at hent
      norm_num at hent
      exact_mod_cast hent
    · have hent := congrFun (congrFun hmat 2) 3
      simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero,
        Matrix.one_apply] at hent
      norm_num at hent
      exact_mod_cast hent
  obtain ⟨rfl, rfl, rfl⟩ := habc0
  have hτ1 : g * ρ⁻¹ = 1 := by
    rw [habc]; simp
  calc g = (g * ρ⁻¹) * ρ := by group
    _ = 1 := by rw [hτ1, hρ1, one_mul]

/-- **The literal base is the affine group**: the presented group on the
twenty displayed relators is isomorphic to the explicit affine matrix
group. -/
noncomputable def baseAffineEquiv : Base ≃* gammaBar :=
  MulEquiv.ofBijective affineQuotient
    ⟨affineQuotient_injective, affineQuotient_surjective⟩

end

end LiteralBaseCompleteness
end GroupApproximation
