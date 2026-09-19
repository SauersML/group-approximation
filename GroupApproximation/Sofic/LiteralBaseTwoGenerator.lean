import GroupApproximation.Sofic.LiteralBaseP13Replay

/-!
# An exact two-generator presentation of the literal rotation group

We perform the Tietze step `u = z`, `v = x * y` inside Lean.  The relators of
the two-generator presentation are defined by literal substitution in the
eight rotation relators.  The finite replay in `LiteralBaseP13Replay` supplies
the only non-formal ingredient: its explicit word recovers `y` from `u,v`.
-/

namespace GroupApproximation
namespace LiteralBaseTwoGenerator

open LiteralBaseRotationRetract LiteralBaseP13Replay

noncomputable section

abbrev TwoGenerator := Fin 2

local instance twoFreeGroupDecidableEq : DecidableEq (FreeGroup TwoGenerator) :=
  Classical.decEq _

abbrev fu : FreeGroup TwoGenerator := FreeGroup.of 0
abbrev fv : FreeGroup TwoGenerator := FreeGroup.of 1

/-- The PEACE recovery word, now regarded as a word in two free generators. -/
abbrev fy : FreeGroup TwoGenerator :=
  (fu * fv * fu * fv⁻¹ * fu⁻¹ * fv * fu⁻¹ * fv⁻¹ * fu⁻¹ * fv⁻¹ * fu⁻¹ * fv) ^ 2

/-- Once `y` is recovered, `x = v * y⁻¹`. -/
abbrev fx : FreeGroup TwoGenerator := fv * fy⁻¹

/-- Substitute `x ↦ fx`, `y ↦ fy`, `z ↦ fu`. -/
def rotationSubstitution : RotationGenerator → FreeGroup TwoGenerator
  | 0 => fx
  | 1 => fy
  | 2 => fu

abbrev rotationSubstitutionHom :
    FreeGroup RotationGenerator →* FreeGroup TwoGenerator :=
  FreeGroup.lift rotationSubstitution

/-- The exact two-generator relator set obtained from the eight rotation
relators by the Tietze substitution. -/
noncomputable def twoRelators : Finset (FreeGroup TwoGenerator) :=
  rotationRelators.image rotationSubstitutionHom

/-- The resulting two-generator presented group. -/
abbrev TwoRotation : Type :=
  PresentedGroup (twoRelators : Set (FreeGroup TwoGenerator))

instance twoRotation_finitelyPresented : Group.IsFinitelyPresented TwoRotation :=
  inferInstance

abbrev twoWord : FreeGroup TwoGenerator →* TwoRotation :=
  PresentedGroup.mk (twoRelators : Set (FreeGroup TwoGenerator))

@[simp] theorem twoWord_of (i : TwoGenerator) :
    twoWord (FreeGroup.of i) = PresentedGroup.of i := rfl

abbrev U : TwoRotation := PresentedGroup.of 0
abbrev V : TwoRotation := PresentedGroup.of 1

/-- Evaluate the two free generators as `Z` and `X * Y` in `Rotation`. -/
def twoGeneratorToRotation : TwoGenerator → Rotation
  | 0 => Z
  | 1 => X * Y

private theorem eval_fy : FreeGroup.lift twoGeneratorToRotation fy = Y := by
  simpa [fy, twoGeneratorToRotation, yFromUZXY, u, v] using yFromUZXY_eq

private theorem eval_fx : FreeGroup.lift twoGeneratorToRotation fx = X := by
  simp [fx, eval_fy, twoGeneratorToRotation]

private theorem eval_substitution (w : FreeGroup RotationGenerator) :
    FreeGroup.lift twoGeneratorToRotation (rotationSubstitutionHom w) =
      rotationWord w := by
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of i =>
      fin_cases i
      · exact eval_fx
      · exact eval_fy
      · simp [rotationSubstitution, twoGeneratorToRotation]
  | inv_of i hi => simpa only [map_inv] using congrArg Inv.inv hi
  | mul a b ha hb => simpa only [map_mul] using congrArg₂ (· * ·) ha hb

theorem twoGeneratorToRotation_kills :
    ∀ q ∈ twoRelators, FreeGroup.lift twoGeneratorToRotation q = 1 := by
  intro q hq
  rw [twoRelators, Finset.mem_image] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  rw [eval_substitution]
  exact rotationRelator_eq_one hr

/-- The canonical homomorphism from the substituted presentation back to the
three-generator rotation presentation. -/
def twoToRotation : TwoRotation →* Rotation :=
  PresentedGroup.toGroup twoGeneratorToRotation_kills

@[simp] theorem twoToRotation_U : twoToRotation U = Z := by
  simp [twoToRotation, twoGeneratorToRotation]

@[simp] theorem twoToRotation_V : twoToRotation V = X * Y := by
  simp [twoToRotation, twoGeneratorToRotation]

/-- Interpret the old rotation generators by their explicit two-generator
words. -/
def rotationGeneratorToTwo (i : RotationGenerator) : TwoRotation :=
  twoWord (rotationSubstitution i)

private theorem lift_rotationGeneratorToTwo (w : FreeGroup RotationGenerator) :
    FreeGroup.lift rotationGeneratorToTwo w =
      twoWord (rotationSubstitutionHom w) := by
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of i => simp [rotationGeneratorToTwo, rotationSubstitutionHom]
  | inv_of i hi => simpa only [map_inv] using congrArg Inv.inv hi
  | mul a b ha hb => simpa only [map_mul] using congrArg₂ (· * ·) ha hb

theorem rotationGeneratorToTwo_kills :
    ∀ r ∈ rotationRelators, FreeGroup.lift rotationGeneratorToTwo r = 1 := by
  intro r hr
  rw [lift_rotationGeneratorToTwo]
  apply PresentedGroup.one_of_mem
  apply Finset.mem_coe.mpr
  change rotationSubstitutionHom r ∈
    rotationRelators.image rotationSubstitutionHom
  exact Finset.mem_image.mpr ⟨r, hr, rfl⟩

/-- The forward Tietze homomorphism from `Rotation` to its substituted
two-generator presentation. -/
def rotationToTwo : Rotation →* TwoRotation :=
  PresentedGroup.toGroup rotationGeneratorToTwo_kills

@[simp] theorem rotationToTwo_X : rotationToTwo X = twoWord fx := by
  simp [rotationToTwo, rotationGeneratorToTwo, rotationSubstitution]

@[simp] theorem rotationToTwo_Y : rotationToTwo Y = twoWord fy := by
  simp [rotationToTwo, rotationGeneratorToTwo, rotationSubstitution]

@[simp] theorem rotationToTwo_Z : rotationToTwo Z = U := by
  simp [rotationToTwo, rotationGeneratorToTwo, rotationSubstitution, U]

private theorem twoToRotation_twoWord (w : FreeGroup TwoGenerator) :
    twoToRotation (twoWord w) = FreeGroup.lift twoGeneratorToRotation w := by
  rfl

private theorem twoWord_fy_mul : twoWord fx * twoWord fy = V := by
  simp [fx, V]

private theorem twoToRotation_comp_rotationToTwo :
    twoToRotation.comp rotationToTwo = MonoidHom.id Rotation := by
  apply MonoidHom.ext
  intro r
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective
    (rotationRelators : Set (FreeGroup RotationGenerator)) r
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of i =>
      fin_cases i
      · change twoToRotation (rotationToTwo X) = X
        rw [rotationToTwo_X, twoToRotation_twoWord, eval_fx]
      · change twoToRotation (rotationToTwo Y) = Y
        rw [rotationToTwo_Y, twoToRotation_twoWord, eval_fy]
      · change twoToRotation (rotationToTwo Z) = Z
        simp
  | inv_of i hi => simpa only [map_inv] using congrArg Inv.inv hi
  | mul a b ha hb => simpa only [map_mul] using congrArg₂ (· * ·) ha hb

private theorem rotationToTwo_comp_twoToRotation :
    rotationToTwo.comp twoToRotation = MonoidHom.id TwoRotation := by
  apply MonoidHom.ext
  intro r
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective
    (twoRelators : Set (FreeGroup TwoGenerator)) r
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of i =>
      fin_cases i
      · change rotationToTwo (twoToRotation U) = U
        simp
      · change rotationToTwo (twoToRotation V) = V
        simpa only [twoToRotation_V, map_mul, rotationToTwo_X,
          rotationToTwo_Y] using twoWord_fy_mul
  | inv_of i hi => simpa only [map_inv] using congrArg Inv.inv hi
  | mul a b ha hb => simpa only [map_mul] using congrArg₂ (· * ·) ha hb

/-- The finite PEACE replay certifies an exact Tietze equivalence between the
literal eight-relator rotation group and its two-generator substituted
presentation. -/
noncomputable def rotationEquivTwoRotation : Rotation ≃* TwoRotation :=
  { rotationToTwo with
    invFun := twoToRotation
    left_inv := fun r ↦ DFunLike.congr_fun twoToRotation_comp_rotationToTwo r
    right_inv := fun r ↦ DFunLike.congr_fun rotationToTwo_comp_twoToRotation r }

end

end LiteralBaseTwoGenerator
end GroupApproximation
