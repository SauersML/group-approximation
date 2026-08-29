import GroupApproximation.Monsters.P13DescentMaster
import GroupApproximation.Sofic.LiteralBaseP13RotationQuotient
import GroupApproximation.Sofic.LiteralBaseAffineQuotient

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
theorem xU_cube : xU ^ 3 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ, pow_succ, pow_one]
  exact GroupApproximation.ExplicitLinearModel.xM_orderThree'

theorem yU_cube : yU ^ 3 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ, pow_succ, pow_one]
  exact GroupApproximation.ExplicitLinearModel.yM_orderThree'

theorem zU_sq : zU ^ 2 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_two]
  exact zM_orderTwo

theorem xU_inv : xU⁻¹ = xU * xU := by
  apply inv_eq_of_mul_eq_one_left
  have h := xU_cube
  rw [pow_succ, pow_two] at h
  exact h

theorem yU_inv : yU⁻¹ = yU * yU := by
  apply inv_eq_of_mul_eq_one_left
  have h := yU_cube
  rw [pow_succ, pow_two] at h
  exact h

/-! ## The rotation matrix model -/

def rotUnit : RotationGenerator → Matˣ
  | 0 => xU
  | 1 => yU
  | 2 => zU

@[simp] theorem rotUnit_zero : rotUnit 0 = xU := rfl
@[simp] theorem rotUnit_one : rotUnit 1 = yU := rfl
@[simp] theorem rotUnit_two : rotUnit 2 = zU := rfl

local macro "verify_unit_matrix" : tactic =>
  `(tactic|
    (ext : 1
     simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one]
     exact Matrix.ext fun i j => by
       fin_cases i <;> fin_cases j <;>
         norm_num [Matrix.mul_apply, Matrix.one_apply, pow_succ,
           Fin.sum_univ_succ, xU, yU, zU, xM, yM, zM]))

private theorem rotUnit_kills_xzcube :
    FreeGroup.lift rotUnit relXZCube = 1 := by
  simp only [relXZCube, map_pow, map_mul, FreeGroup.lift_apply_of,
    rotUnit_zero, rotUnit_two]
  verify_unit_matrix

private theorem rotUnit_kills_yzcube :
    FreeGroup.lift rotUnit relYZCube = 1 := by
  simp only [relYZCube, map_pow, map_mul, FreeGroup.lift_apply_of,
    rotUnit_one, rotUnit_two]
  verify_unit_matrix

private theorem rotUnit_kills_xinvzxy :
    FreeGroup.lift rotUnit relXInvZXY = 1 := by
  simp only [relXInvZXY, map_pow, map_mul, map_inv, FreeGroup.lift_apply_of,
    rotUnit_zero, rotUnit_one, rotUnit_two]
  rw [xU_inv]
  verify_unit_matrix

private theorem rotUnit_kills_yinvzyx :
    FreeGroup.lift rotUnit relYInvZYX = 1 := by
  simp only [relYInvZYX, map_pow, map_mul, map_inv, FreeGroup.lift_apply_of,
    rotUnit_zero, rotUnit_one, rotUnit_two]
  rw [yU_inv]
  verify_unit_matrix

private theorem rotUnit_kills_xysix :
    FreeGroup.lift rotUnit relXYSix = 1 := by
  simp only [relXYSix, map_pow, map_mul, FreeGroup.lift_apply_of,
    rotUnit_zero, rotUnit_one]
  verify_unit_matrix

theorem rotUnit_kills :
    ∀ r ∈ (rotationRelators : Set (FreeGroup RotationGenerator)),
      FreeGroup.lift rotUnit r = 1 := by
  intro r hr
  have hr' : r ∈ rotationRelators := hr
  rw [mem_rotationRelators_iff] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [relXCube, map_pow, FreeGroup.lift_apply_of,
      rotUnit_zero] using xU_cube
  · simpa only [relYCube, map_pow, FreeGroup.lift_apply_of,
      rotUnit_one] using yU_cube
  · simpa only [relZSq, map_pow, FreeGroup.lift_apply_of,
      rotUnit_two] using zU_sq
  · exact rotUnit_kills_xzcube
  · exact rotUnit_kills_yzcube
  · exact rotUnit_kills_xinvzxy
  · exact rotUnit_kills_yinvzyx
  · exact rotUnit_kills_xysix

/-- The matrix model of the abstract eight-relator rotation group. -/
def rotationToMat : Rotation →* Matˣ :=
  PresentedGroup.toGroup rotUnit_kills

@[simp] theorem rotationToMat_X : rotationToMat X = xU :=
  PresentedGroup.toGroup.of rotUnit_kills

@[simp] theorem rotationToMat_Y : rotationToMat Y = yU :=
  PresentedGroup.toGroup.of rotUnit_kills

@[simp] theorem rotationToMat_Z : rotationToMat Z = zU :=
  PresentedGroup.toGroup.of rotUnit_kills

theorem rotationToMat_word (w : FreeGroup RotationGenerator) :
    rotationToMat (rotationWord w) = FreeGroup.lift rotUnit w := by
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of i =>
      rw [rotationWord_of, FreeGroup.lift_apply_of]
      match i with
      | 0 => exact rotationToMat_X
      | 1 => exact rotationToMat_Y
      | 2 => exact rotationToMat_Z
  | inv_of i h => simpa only [map_inv] using congrArg Inv.inv h
  | mul a b ha hb => simpa only [map_mul] using congrArg₂ (· * ·) ha hb

/-! ## The block embedding of `SL₃(ℤ)` -/

def blockMonoid : Matrix (Fin 3) (Fin 3) ℚ →* Mat where
  toFun A :=
    (Matrix.fromBlocks A (0 : Matrix (Fin 3) (Fin 1) ℚ)
      (0 : Matrix (Fin 1) (Fin 3) ℚ)
      (1 : Matrix (Fin 1) (Fin 1) ℚ)).submatrix
      (finSumFinEquiv (m := 3) (n := 1)).symm
      (finSumFinEquiv (m := 3) (n := 1)).symm
  map_one' := by
    have h1 : Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) ℚ)
        (0 : Matrix (Fin 3) (Fin 1) ℚ) (0 : Matrix (Fin 1) (Fin 3) ℚ)
        (1 : Matrix (Fin 1) (Fin 1) ℚ) =
        (1 : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℚ) :=
      Matrix.fromBlocks_one
    rw [h1]
    have h2 : ((1 : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℚ)).submatrix
        (finSumFinEquiv (m := 3) (n := 1)).symm
        (finSumFinEquiv (m := 3) (n := 1)).symm = (1 : Mat) :=
      Matrix.submatrix_one_equiv _
    exact h2
  map_mul' A B := by
    rw [Matrix.submatrix_mul_equiv
      (Matrix.fromBlocks A (0 : Matrix (Fin 3) (Fin 1) ℚ)
        (0 : Matrix (Fin 1) (Fin 3) ℚ) (1 : Matrix (Fin 1) (Fin 1) ℚ))
      (Matrix.fromBlocks B (0 : Matrix (Fin 3) (Fin 1) ℚ)
        (0 : Matrix (Fin 1) (Fin 3) ℚ) (1 : Matrix (Fin 1) (Fin 1) ℚ))
      (finSumFinEquiv (m := 3) (n := 1)).symm
      (finSumFinEquiv (m := 3) (n := 1)).symm
      (finSumFinEquiv (m := 3) (n := 1)).symm,
      Matrix.fromBlocks_multiply]
    simp

def castMat (A : Matrix (Fin 3) (Fin 3) ℤ) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  A.map (Int.cast : ℤ → ℚ)

theorem castMat_mul (A B : Matrix (Fin 3) (Fin 3) ℤ) :
    castMat (A * B) = castMat A * castMat B := by
  refine Matrix.ext fun i j => ?_
  simp only [castMat, Matrix.map_apply, Matrix.mul_apply]
  push_cast
  rfl

theorem castMat_one : castMat 1 = 1 := by
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j <;>
    simp [castMat, Matrix.map_apply, Matrix.one_apply, h]

theorem sl3_coe_mul_inv (A : SL3) :
    (A : Matrix (Fin 3) (Fin 3) ℤ) *
      ((A⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℤ) = 1 :=
  calc (A : Matrix (Fin 3) (Fin 3) ℤ) *
      ((A⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℤ)
      = ((A * A⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℤ) := by
        rw [Matrix.SpecialLinearGroup.coe_mul]
    _ = ((1 : SL3) : Matrix (Fin 3) (Fin 3) ℤ) := by
        rw [mul_inv_cancel]
    _ = 1 := rfl

theorem sl3_coe_inv_mul (A : SL3) :
    ((A⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℤ) *
      (A : Matrix (Fin 3) (Fin 3) ℤ) = 1 :=
  calc ((A⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℤ) *
      (A : Matrix (Fin 3) (Fin 3) ℤ)
      = ((A⁻¹ * A : SL3) : Matrix (Fin 3) (Fin 3) ℤ) := by
        rw [Matrix.SpecialLinearGroup.coe_mul]
    _ = ((1 : SL3) : Matrix (Fin 3) (Fin 3) ℤ) := by
        rw [inv_mul_cancel]
    _ = 1 := rfl

/-- The `4 × 4` affine block embedding of the integral special linear
group, with definitionally transparent value. -/
def blockEmbed4 : SL3 →* Matˣ where
  toFun A :=
    { val := blockMonoid (castMat (A : Matrix (Fin 3) (Fin 3) ℤ))
      inv := blockMonoid (castMat ((A⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℤ))
      val_inv := by
        rw [← map_mul, ← castMat_mul, sl3_coe_mul_inv, castMat_one, map_one]
      inv_val := by
        rw [← map_mul, ← castMat_mul, sl3_coe_inv_mul, castMat_one, map_one] }
  map_one' := by
    refine Units.ext ?_
    show blockMonoid (castMat ((1 : SL3) : Matrix (Fin 3) (Fin 3) ℤ)) = 1
    rw [show ((1 : SL3) : Matrix (Fin 3) (Fin 3) ℤ) = 1 from rfl,
      castMat_one, map_one]
  map_mul' A B := by
    refine Units.ext ?_
    show blockMonoid (castMat ((A * B : SL3) : Matrix (Fin 3) (Fin 3) ℤ)) = _
    rw [show ((A * B : SL3) : Matrix (Fin 3) (Fin 3) ℤ) =
        (A : Matrix (Fin 3) (Fin 3) ℤ) * (B : Matrix (Fin 3) (Fin 3) ℤ) from
      Matrix.SpecialLinearGroup.coe_mul A B, castMat_mul, map_mul]
    rfl

@[simp] theorem blockEmbed4_val (A : SL3) :
    (blockEmbed4 A).val =
      blockMonoid (castMat (A : Matrix (Fin 3) (Fin 3) ℤ)) := rfl

/-- Explicit entries of the block embedding. -/
theorem blockEmbed4_val_explicit (A : SL3) :
    ((blockEmbed4 A : Matˣ) : Mat) =
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
  rw [blockEmbed4_val]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [blockMonoid, Matrix.submatrix_apply, Matrix.fromBlocks,
      finSumFinEquiv, Fin.addCases, castMat, Matrix.map_apply]

/-! ## The compatibility square -/

/-- The affine evaluation composed through the embedded rotations is the
rotation matrix model, by uniqueness of presented-group lifts. -/
theorem affineQuotient_rotationToBase_hom :
    gammaBar.subtype.comp (affineQuotient.comp rotationToBase) =
      rotationToMat := by
  have hgen : ∀ i : RotationGenerator,
      (gammaBar.subtype.comp (affineQuotient.comp rotationToBase))
        (PresentedGroup.of i) = rotUnit i := by
    intro i
    match i with
    | 0 =>
        show ((affineQuotient (rotationToBase X) : gammaBar) : Matˣ) =
          rotUnit 0
        rw [rotationToBase_X]
        have hg : affineQuotient (x : Base) = xG := by
          show affineQuotient
            (PresentedGroup.of LiteralNonMFPresentation.xIndex) = xG
          rw [affineQuotient_generator, matrixBaseGenerator_x]
        rw [hg]
        rfl
    | 1 =>
        show ((affineQuotient (rotationToBase Y) : gammaBar) : Matˣ) =
          rotUnit 1
        rw [rotationToBase_Y]
        have hg : affineQuotient (y : Base) = yG := by
          show affineQuotient
            (PresentedGroup.of LiteralNonMFPresentation.yIndex) = yG
          rw [affineQuotient_generator, matrixBaseGenerator_y]
        rw [hg]
        rfl
    | 2 =>
        show ((affineQuotient (rotationToBase Z) : gammaBar) : Matˣ) =
          rotUnit 2
        rw [rotationToBase_Z]
        have hg : affineQuotient (z : Base) = zG := by
          show affineQuotient
            (PresentedGroup.of LiteralNonMFPresentation.zIndex) = zG
          rw [affineQuotient_generator, matrixBaseGenerator_z]
        rw [hg]
        rfl
  exact MonoidHom.ext fun r =>
    PresentedGroup.toGroup.unique rotUnit_kills
      (gammaBar.subtype.comp (affineQuotient.comp rotationToBase)) hgen

theorem affineQuotient_rotationToBase (r : Rotation) :
    ((affineQuotient (rotationToBase r) : gammaBar) : Matˣ) =
      rotationToMat r :=
  DFunLike.congr_fun affineQuotient_rotationToBase_hom r

/-! ## The six letter evaluations -/

local macro "verify_word_matrix" : tactic =>
  `(tactic|
    (refine Units.ext ?_
     simp only [Units.val_mul, Units.val_one]
     rw [blockEmbed4_val_explicit]
     exact Matrix.ext fun i j => by
       fin_cases i <;> fin_cases j <;>
         norm_num [Matrix.mul_apply, Fin.sum_univ_succ, elem,
           xU, yU, zU, xM, yM, zM, Matrix.cons_val_zero,
           Matrix.cons_val_one, Matrix.cons_val_two,
           Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]))

private theorem rotationToMat_p13_0 :
    rotationToMat (p13ToRotation (PresentedGroup.of (0 : P13Generator))) =
      blockEmbed4 (elem (0 : P13Generator)) := by
  rw [p13ToRotation_E12_word, rotationToMat_word]
  have hw : rotationSignedWord "YxzYX" = [((1 : Fin 3), false), ((0 : Fin 3), true), ((2 : Fin 3), true), ((1 : Fin 3), false), ((0 : Fin 3), false)] := by decide
  rw [hw]
  show FreeGroup.lift rotUnit (FreeGroup.mk [((1 : Fin 3), false), ((0 : Fin 3), true), ((2 : Fin 3), true), ((1 : Fin 3), false), ((0 : Fin 3), false)]) =
    blockEmbed4 (elem 0)
  rw [FreeGroup.lift_mk]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    cond_true, cond_false, mul_one, rotUnit_zero, rotUnit_one,
    rotUnit_two]
  rw [yU_inv, xU_inv]
  verify_word_matrix

private theorem rotationToMat_p13_1 :
    rotationToMat (p13ToRotation (PresentedGroup.of (1 : P13Generator))) =
      blockEmbed4 (elem (1 : P13Generator)) := by
  rw [p13ToRotation_E13_word, rotationToMat_word]
  have hw : rotationSignedWord "xzYXY" = [((0 : Fin 3), true), ((2 : Fin 3), true), ((1 : Fin 3), false), ((0 : Fin 3), false), ((1 : Fin 3), false)] := by decide
  rw [hw]
  show FreeGroup.lift rotUnit (FreeGroup.mk [((0 : Fin 3), true), ((2 : Fin 3), true), ((1 : Fin 3), false), ((0 : Fin 3), false), ((1 : Fin 3), false)]) =
    blockEmbed4 (elem 1)
  rw [FreeGroup.lift_mk]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    cond_true, cond_false, mul_one, rotUnit_zero, rotUnit_one,
    rotUnit_two]
  rw [yU_inv, xU_inv]
  verify_word_matrix

private theorem rotationToMat_p13_2 :
    rotationToMat (p13ToRotation (PresentedGroup.of (2 : P13Generator))) =
      blockEmbed4 (elem (2 : P13Generator)) := by
  rw [p13ToRotation_E21_word, rotationToMat_word]
  have hw : rotationSignedWord "Yxyxz" = [((1 : Fin 3), false), ((0 : Fin 3), true), ((1 : Fin 3), true), ((0 : Fin 3), true), ((2 : Fin 3), true)] := by decide
  rw [hw]
  show FreeGroup.lift rotUnit (FreeGroup.mk [((1 : Fin 3), false), ((0 : Fin 3), true), ((1 : Fin 3), true), ((0 : Fin 3), true), ((2 : Fin 3), true)]) =
    blockEmbed4 (elem 2)
  rw [FreeGroup.lift_mk]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    cond_true, cond_false, mul_one, rotUnit_zero, rotUnit_one,
    rotUnit_two]
  rw [yU_inv]
  verify_word_matrix

private theorem rotationToMat_p13_3 :
    rotationToMat (p13ToRotation (PresentedGroup.of (3 : P13Generator))) =
      blockEmbed4 (elem (3 : P13Generator)) := by
  rw [p13ToRotation_E23_word, rotationToMat_word]
  have hw : rotationSignedWord "XYxzY" = [((0 : Fin 3), false), ((1 : Fin 3), false), ((0 : Fin 3), true), ((2 : Fin 3), true), ((1 : Fin 3), false)] := by decide
  rw [hw]
  show FreeGroup.lift rotUnit (FreeGroup.mk [((0 : Fin 3), false), ((1 : Fin 3), false), ((0 : Fin 3), true), ((2 : Fin 3), true), ((1 : Fin 3), false)]) =
    blockEmbed4 (elem 3)
  rw [FreeGroup.lift_mk]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    cond_true, cond_false, mul_one, rotUnit_zero, rotUnit_one,
    rotUnit_two]
  rw [yU_inv, xU_inv]
  verify_word_matrix

private theorem rotationToMat_p13_4 :
    rotationToMat (p13ToRotation (PresentedGroup.of (4 : P13Generator))) =
      blockEmbed4 (elem (4 : P13Generator)) := by
  rw [p13ToRotation_E31_word, rotationToMat_word]
  have hw : rotationSignedWord "xYxzYx" = [((0 : Fin 3), true), ((1 : Fin 3), false), ((0 : Fin 3), true), ((2 : Fin 3), true), ((1 : Fin 3), false), ((0 : Fin 3), true)] := by decide
  rw [hw]
  show FreeGroup.lift rotUnit (FreeGroup.mk [((0 : Fin 3), true), ((1 : Fin 3), false), ((0 : Fin 3), true), ((2 : Fin 3), true), ((1 : Fin 3), false), ((0 : Fin 3), true)]) =
    blockEmbed4 (elem 4)
  rw [FreeGroup.lift_mk]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    cond_true, cond_false, mul_one, rotUnit_zero, rotUnit_one,
    rotUnit_two]
  rw [yU_inv]
  verify_word_matrix

private theorem rotationToMat_p13_5 :
    rotationToMat (p13ToRotation (PresentedGroup.of (5 : P13Generator))) =
      blockEmbed4 (elem (5 : P13Generator)) := by
  rw [p13ToRotation_E32_word, rotationToMat_word]
  have hw : rotationSignedWord "XzYXYX" = [((0 : Fin 3), false), ((2 : Fin 3), true), ((1 : Fin 3), false), ((0 : Fin 3), false), ((1 : Fin 3), false), ((0 : Fin 3), false)] := by decide
  rw [hw]
  show FreeGroup.lift rotUnit (FreeGroup.mk [((0 : Fin 3), false), ((2 : Fin 3), true), ((1 : Fin 3), false), ((0 : Fin 3), false), ((1 : Fin 3), false), ((0 : Fin 3), false)]) =
    blockEmbed4 (elem 5)
  rw [FreeGroup.lift_mk]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    cond_true, cond_false, mul_one, rotUnit_zero, rotUnit_one,
    rotUnit_two]
  rw [yU_inv, xU_inv]
  verify_word_matrix

/-- The Steinberg letters evaluate through the rotation words to the
block elementary matrices. -/
theorem rotationToMat_p13 (i : P13Generator) :
    rotationToMat (p13ToRotation (PresentedGroup.of i)) =
      blockEmbed4 (elem i) := by
  match i with
  | 0 => exact rotationToMat_p13_0
  | 1 => exact rotationToMat_p13_1
  | 2 => exact rotationToMat_p13_2
  | 3 => exact rotationToMat_p13_3
  | 4 => exact rotationToMat_p13_4
  | 5 => exact rotationToMat_p13_5
/-- The full compatibility square, as an equality of homomorphisms out
of the Steinberg presentation. -/
theorem rotationToMat_comp_p13ToRotation :
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

/-! ## The translation units -/

def transMat (q₁ q₂ q₃ : ℚ) : Mat :=
  !![1, 0, 0, q₁; 0, 1, 0, q₂; 0, 0, 1, q₃; 0, 0, 0, 1]

theorem transMat_mul (p₁ p₂ p₃ q₁ q₂ q₃ : ℚ) :
    transMat p₁ p₂ p₃ * transMat q₁ q₂ q₃ =
      transMat (p₁ + q₁) (p₂ + q₂) (p₃ + q₃) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    norm_num [transMat, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

def transUnit (q₁ q₂ q₃ : ℚ) : Matˣ where
  val := transMat q₁ q₂ q₃
  inv := transMat (-q₁) (-q₂) (-q₃)
  val_inv := by
    rw [transMat_mul]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      norm_num [transMat, Matrix.one_apply]
  inv_val := by
    rw [transMat_mul]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      norm_num [transMat, Matrix.one_apply]

theorem transUnit_mul (p₁ p₂ p₃ q₁ q₂ q₃ : ℚ) :
    transUnit p₁ p₂ p₃ * transUnit q₁ q₂ q₃ =
      transUnit (p₁ + q₁) (p₂ + q₂) (p₃ + q₃) :=
  Units.ext (transMat_mul p₁ p₂ p₃ q₁ q₂ q₃)

theorem transUnit_inv (q₁ q₂ q₃ : ℚ) :
    (transUnit q₁ q₂ q₃)⁻¹ = transUnit (-q₁) (-q₂) (-q₃) :=
  Units.ext rfl

theorem transUnit_zpow₁ (a : ℤ) :
    transUnit 1 0 0 ^ a = transUnit (a : ℚ) 0 0 := by
  induction a using Int.induction_on with
  | zero =>
      rw [zpow_zero]
      refine Units.ext ?_
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        norm_num [transUnit, transMat, Matrix.one_apply]
  | succ n ih =>
      rw [zpow_add_one, ih, transUnit_mul]
      congr 1 <;> push_cast <;> ring
  | pred n ih =>
      rw [zpow_sub_one, ih, transUnit_inv, transUnit_mul]
      congr 1 <;> push_cast <;> ring

theorem transUnit_zpow₂ (b : ℤ) :
    transUnit 0 1 0 ^ b = transUnit 0 (b : ℚ) 0 := by
  induction b using Int.induction_on with
  | zero =>
      rw [zpow_zero]
      refine Units.ext ?_
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        norm_num [transUnit, transMat, Matrix.one_apply]
  | succ n ih =>
      rw [zpow_add_one, ih, transUnit_mul]
      congr 1 <;> push_cast <;> ring
  | pred n ih =>
      rw [zpow_sub_one, ih, transUnit_inv, transUnit_mul]
      congr 1 <;> push_cast <;> ring

theorem transUnit_zpow₃ (c : ℤ) :
    transUnit 0 0 1 ^ c = transUnit 0 0 (c : ℚ) := by
  induction c using Int.induction_on with
  | zero =>
      rw [zpow_zero]
      refine Units.ext ?_
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        norm_num [transUnit, transMat, Matrix.one_apply]
  | succ n ih =>
      rw [zpow_add_one, ih, transUnit_mul]
      congr 1 <;> push_cast <;> ring
  | pred n ih =>
      rw [zpow_sub_one, ih, transUnit_inv, transUnit_mul]
      congr 1 <;> push_cast <;> ring

theorem v1U_eq_transUnit : v1U = transUnit 1 0 0 := by
  refine Units.ext ?_
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    norm_num [v1U, transUnit, v1M, transMat]

theorem v2U_eq_transUnit : v2U = transUnit 0 1 0 := by
  refine Units.ext ?_
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    norm_num [v2U, transUnit, v2M, transMat]

theorem v3U_eq_transUnit : v3U = transUnit 0 0 1 := by
  refine Units.ext ?_
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    norm_num [v3U, transUnit, v3M, transMat]

theorem vprod_val (a b c : ℤ) :
    ((v1U ^ a * v2U ^ b * v3U ^ c : Matˣ) : Mat) =
      transMat (a : ℚ) (b : ℚ) (c : ℚ) := by
  rw [v1U_eq_transUnit, v2U_eq_transUnit, v3U_eq_transUnit,
    transUnit_zpow₁, transUnit_zpow₂, transUnit_zpow₃,
    transUnit_mul, transUnit_mul]
  show transMat _ _ _ = _
  congr 1 <;> ring

/-! ## The translation normal form -/

/-- Every element of the translation subgroup is a triple power of the
three commuting translation letters. -/
theorem exists_translation_form {τ : Base}
    (hτ : τ ∈ translations) :
    ∃ a b c : ℤ, τ = v1 ^ a * v2 ^ b * v3 ^ c := by
  have h12 : Commute (v1 : Base) v2 := v1_commutes_translations v2_mem_translations
  have h13 : Commute (v1 : Base) v3 := v1_commutes_translations v3_mem_translations
  have h23 : Commute (v2 : Base) v3 := v2_commutes_translations v3_mem_translations
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
      have hc2 : Commute ((v3 : Base) ^ c) (v2 ^ b') :=
        h23.symm.zpow_zpow c b'
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
            rw [_root_.mul_inv_rev, _root_.mul_inv_rev]; group
        _ = (v2 ^ b)⁻¹ * (v3 ^ c)⁻¹ * (v1 ^ a)⁻¹ := by rw [i23]
        _ = (v2 ^ b)⁻¹ * ((v3 ^ c)⁻¹ * (v1 ^ a)⁻¹) := by group
        _ = (v2 ^ b)⁻¹ * ((v1 ^ a)⁻¹ * (v3 ^ c)⁻¹) := by rw [i13]
        _ = (v2 ^ b)⁻¹ * (v1 ^ a)⁻¹ * (v3 ^ c)⁻¹ := by group
        _ = (v1 ^ a)⁻¹ * (v2 ^ b)⁻¹ * (v3 ^ c)⁻¹ := by rw [i12]

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
  have hρval : ((affineQuotient ρ : gammaBar) : Matˣ) =
      blockEmbed4 (toSL3 p) := by
    rw [hρdef, ← hp, affineQuotient_rotationToBase]
    have := DFunLike.congr_fun rotationToMat_comp_p13ToRotation p
    simpa only [MonoidHom.comp_apply] using this
  have hτval : ((affineQuotient (g * ρ⁻¹) : gammaBar) : Matˣ) =
      v1U ^ a * v2U ^ b * v3U ^ c := by
    rw [habc]
    have h1 : affineQuotient (v1 : Base) = v1G := by
      show affineQuotient
        (PresentedGroup.of LiteralNonMFPresentation.v1Index) = v1G
      rw [affineQuotient_generator, matrixBaseGenerator_v1]
    have h2 : affineQuotient (v2 : Base) = v2G := by
      show affineQuotient
        (PresentedGroup.of LiteralNonMFPresentation.v2Index) = v2G
      rw [affineQuotient_generator, matrixBaseGenerator_v2]
    have h3 : affineQuotient (v3 : Base) = v3G := by
      show affineQuotient
        (PresentedGroup.of LiteralNonMFPresentation.v3Index) = v3G
      rw [affineQuotient_generator, matrixBaseGenerator_v3]
    rw [map_mul, map_mul, _root_.map_zpow, _root_.map_zpow,
      _root_.map_zpow, h1, h2, h3]
    simp only [MulMemClass.coe_mul, SubgroupClass.coe_zpow]
    rfl
  have hprod : (v1U ^ a * v2U ^ b * v3U ^ c) * blockEmbed4 (toSL3 p) =
      1 := by
    have h2 : affineQuotient (g * ρ⁻¹) * affineQuotient ρ = 1 := by
      rw [← map_mul, ← hgdecomp, hg]
    calc (v1U ^ a * v2U ^ b * v3U ^ c) * blockEmbed4 (toSL3 p)
        = ((affineQuotient (g * ρ⁻¹) : gammaBar) : Matˣ) *
            ((affineQuotient ρ : gammaBar) : Matˣ) := by
          rw [hτval, hρval]
      _ = ((affineQuotient (g * ρ⁻¹) * affineQuotient ρ :
            gammaBar) : Matˣ) := by
          rw [MulMemClass.coe_mul]
      _ = ((1 : gammaBar) : Matˣ) := by rw [h2]
      _ = 1 := rfl
  have hmat : transMat (a : ℚ) (b : ℚ) (c : ℚ) *
      ((blockEmbed4 (toSL3 p) : Matˣ) : Mat) = 1 := by
    have hval := congrArg (fun u : Matˣ => (u : Mat)) hprod
    rw [show ((((v1U ^ a * v2U ^ b * v3U ^ c) *
        blockEmbed4 (toSL3 p) : Matˣ)) : Mat) =
      ((v1U ^ a * v2U ^ b * v3U ^ c : Matˣ) : Mat) *
        ((blockEmbed4 (toSL3 p) : Matˣ) : Mat) from Units.val_mul _ _,
      vprod_val] at hval
    simpa using hval
  rw [blockEmbed4_val_explicit] at hmat
  have hcorner : toSL3 p = 1 := by
    ext i j
    match i, j with
    | 0, 0 =>
        have hE := congrFun (congrFun hmat 0) 0
        norm_num [transMat, Matrix.mul_apply, Fin.sum_univ_succ,
          Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
          Matrix.tail_cons] at hE ⊢
        exact_mod_cast hE
    | 0, 1 =>
        have hE := congrFun (congrFun hmat 0) 1
        norm_num [transMat, Matrix.mul_apply, Fin.sum_univ_succ,
          Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
          Matrix.tail_cons] at hE ⊢
        exact_mod_cast hE
    | 0, 2 =>
        have hE := congrFun (congrFun hmat 0) 2
        norm_num [transMat, Matrix.mul_apply, Fin.sum_univ_succ,
          Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
          Matrix.tail_cons] at hE ⊢
        exact_mod_cast hE
    | 1, 0 =>
        have hE := congrFun (congrFun hmat 1) 0
        norm_num [transMat, Matrix.mul_apply, Fin.sum_univ_succ,
          Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
          Matrix.tail_cons] at hE ⊢
        exact_mod_cast hE
    | 1, 1 =>
        have hE := congrFun (congrFun hmat 1) 1
        norm_num [transMat, Matrix.mul_apply, Fin.sum_univ_succ,
          Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
          Matrix.tail_cons] at hE ⊢
        exact_mod_cast hE
    | 1, 2 =>
        have hE := congrFun (congrFun hmat 1) 2
        norm_num [transMat, Matrix.mul_apply, Fin.sum_univ_succ,
          Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
          Matrix.tail_cons] at hE ⊢
        exact_mod_cast hE
    | 2, 0 =>
        have hE := congrFun (congrFun hmat 2) 0
        norm_num [transMat, Matrix.mul_apply, Fin.sum_univ_succ,
          Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
          Matrix.tail_cons] at hE ⊢
        exact_mod_cast hE
    | 2, 1 =>
        have hE := congrFun (congrFun hmat 2) 1
        norm_num [transMat, Matrix.mul_apply, Fin.sum_univ_succ,
          Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
          Matrix.tail_cons] at hE ⊢
        exact_mod_cast hE
    | 2, 2 =>
        have hE := congrFun (congrFun hmat 2) 2
        norm_num [transMat, Matrix.mul_apply, Fin.sum_univ_succ,
          Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
          Matrix.tail_cons] at hE ⊢
        exact_mod_cast hE
  have hp1 : p = 1 :=
    (injective_iff_map_eq_one toSL3).mp P13DescentMaster.toSL3_injective
      p hcorner
  have hρ1 : ρ = 1 := by
    rw [hρdef, ← hp, hp1, map_one, map_one]
  rw [hcorner] at hmat
  have habc0 : a = 0 ∧ b = 0 ∧ c = 0 := by
    refine ⟨?_, ?_, ?_⟩
    · have hE := congrFun (congrFun hmat 0) 3
      norm_num [transMat, Matrix.mul_apply, Fin.sum_univ_succ,
        Matrix.one_apply, Matrix.SpecialLinearGroup.coe_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hE
      exact_mod_cast hE
    · have hE := congrFun (congrFun hmat 1) 3
      norm_num [transMat, Matrix.mul_apply, Fin.sum_univ_succ,
        Matrix.one_apply, Matrix.SpecialLinearGroup.coe_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hE
      exact_mod_cast hE
    · have hE := congrFun (congrFun hmat 2) 3
      norm_num [transMat, Matrix.mul_apply, Fin.sum_univ_succ,
        Matrix.one_apply, Matrix.SpecialLinearGroup.coe_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hE
      exact_mod_cast hE
  obtain ⟨rfl, rfl, rfl⟩ := habc0
  calc g = (g * ρ⁻¹) * ρ := by group
    _ = 1 := by rw [habc, hρ1]; simp

/-- **The literal base is the affine group**: the presented group on the
twenty displayed relators is isomorphic to the explicit affine matrix
group. -/
noncomputable def baseAffineEquiv : Base ≃* gammaBar :=
  MulEquiv.ofBijective affineQuotient
    ⟨affineQuotient_injective, affineQuotient_surjective⟩

end

end LiteralBaseCompleteness
end GroupApproximation
