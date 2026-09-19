import GroupApproximation.Sofic.LiteralBaseP13Replay
import GroupApproximation.Sofic.LiteralP13Presentation
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S123
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S132
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S213
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S231
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S312
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S321
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O12_13
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O12_32
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O13_23
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O21_23
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O21_31
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O31_32
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.Torsion
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.RangeZ
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.RangeXY

/-!
# The literal P13 presentation maps onto the rotation presentation

The six P13 letters map to the following words in the abstract eight-relator
rotation presentation:

`e12 = YxzYX`, `e13 = xzYXY`, `e21 = Yxyxz`,
`e23 = XYxzY`, `e31 = xYxzYx`, `e32 = XzYXYX`.

The imported replay modules prove, within the abstract rotation presentation,
that all thirteen P13 relators vanish under this substitution.  The same
proof-carrying replay checks explicit preimages of `Z` and `X * Y`; these two
elements generate the rotation presentation.  Thus the induced homomorphism
is surjective.  No matrix equality or external presentation theorem is used.
-/

namespace GroupApproximation
namespace LiteralBaseP13RotationQuotient

open LiteralP13Presentation LiteralBaseRotationRetract LiteralBaseP13Replay
open LiteralBaseP13RotationReplay PresentedGroupRelatorReplay

noncomputable section

private def e12Word : FreeGroup RotationGenerator :=
  word (rotationSignedWord "YxzYX")
private def e13Word : FreeGroup RotationGenerator :=
  word (rotationSignedWord "xzYXY")
private def e21Word : FreeGroup RotationGenerator :=
  word (rotationSignedWord "Yxyxz")
private def e23Word : FreeGroup RotationGenerator :=
  word (rotationSignedWord "XYxzY")
private def e31Word : FreeGroup RotationGenerator :=
  word (rotationSignedWord "xYxzYx")
private def e32Word : FreeGroup RotationGenerator :=
  word (rotationSignedWord "XzYXYX")

private def p13GeneratorToFreeRotation :
    P13Generator → FreeGroup RotationGenerator
  | 0 => e12Word
  | 1 => e13Word
  | 2 => e21Word
  | 3 => e23Word
  | 4 => e31Word
  | 5 => e32Word

private def p13FreeMap : FreeGroup P13Generator →* FreeGroup RotationGenerator :=
  FreeGroup.lift p13GeneratorToFreeRotation

/-- Evaluate the six P13 letters at the audited short words in `Rotation`. -/
def p13GeneratorToRotation (i : P13Generator) : Rotation :=
  rotationWord (p13GeneratorToFreeRotation i)

private theorem lift_p13GeneratorToRotation :
    FreeGroup.lift p13GeneratorToRotation = rotationWord.comp p13FreeMap := by
  ext i
  simp [p13GeneratorToRotation, p13FreeMap]

private def p13RelatorRotationWord :
    Fin 13 → FreeGroup RotationGenerator
  | 0 => word (rotationSignedWord "YxzYXXYxzYxyZXyyZXyxyxyZX")
  | 1 => word (rotationSignedWord "xzYXYXzYXYXyxyZyxyZxxyZXy")
  | 2 => word (rotationSignedWord "YxyxzxzYXYZXYXyyxyZXyZXyx")
  | 3 => word (rotationSignedWord "XYxzYxYxzYxyZXyyZXyXZXYXy")
  | 4 => word (rotationSignedWord "xYxzYxYxzYXXyZXyyZXyxyxyZx")
  | 5 => word (rotationSignedWord "XzYXYXYxyxzxyxyZxZXYXyXyZXyX")
  | 6 => word (rotationSignedWord "YxzYzYXYxyZXyyxyZX")
  | 7 => word (rotationSignedWord "YxzYXXzYXZXyxyxyZx")
  | 8 => word (rotationSignedWord "xzYXYXYxzxyZXyZXyx")
  | 9 => word (rotationSignedWord "YxyxzXYxzYZXYXyyZXyx")
  | 10 => word (rotationSignedWord "YxyxzxYxzYxZXYXyXyZXyX")
  | 11 => word (rotationSignedWord "xYxzYzYXYXXyZXyyxyZx")
  | 12 => word (rotationSignedWord
      "YxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX")

private theorem p13FreeMap_relator (i : Fin 13) :
    p13FreeMap (p13Relator i) = p13RelatorRotationWord i := by
  fin_cases i <;> decide

private theorem p13RelatorRotationWord_image_eq_one (i : Fin 13) :
    rotationWord (p13RelatorRotationWord i) = 1 := by
  fin_cases i
  · exact s123Image_eq_one
  · exact s132Image_eq_one
  · exact s213Image_eq_one
  · exact s231Image_eq_one
  · exact s312Image_eq_one
  · exact s321Image_eq_one
  · exact o12_13Image_eq_one
  · exact o12_32Image_eq_one
  · exact o13_23Image_eq_one
  · exact o21_23Image_eq_one
  · exact o21_31Image_eq_one
  · exact o31_32Image_eq_one
  · exact torsionImage_eq_one

/-- Every literal P13 relator vanishes after the corrected short-word
substitution. -/
theorem p13GeneratorToRotation_kills :
    ∀ r ∈ p13Relators, FreeGroup.lift p13GeneratorToRotation r = 1 := by
  intro r hr
  obtain ⟨i, rfl⟩ := (mem_p13Relators_iff r).mp hr
  rw [lift_p13GeneratorToRotation, MonoidHom.comp_apply,
    p13FreeMap_relator]
  exact p13RelatorRotationWord_image_eq_one i

/-- The canonical homomorphism from P13 to the abstract rotation group. -/
def p13ToRotation : P13 →* Rotation :=
  PresentedGroup.toGroup p13GeneratorToRotation_kills

private theorem p13ToRotation_generator (i : P13Generator) :
    p13ToRotation (PresentedGroup.of i) = p13GeneratorToRotation i := by
  simp [p13ToRotation]

@[simp] theorem p13ToRotation_E12 : p13ToRotation E12 = rotationWord e12Word :=
  p13ToRotation_generator 0

@[simp] theorem p13ToRotation_E13 : p13ToRotation E13 = rotationWord e13Word :=
  p13ToRotation_generator 1

@[simp] theorem p13ToRotation_E21 : p13ToRotation E21 = rotationWord e21Word :=
  p13ToRotation_generator 2

@[simp] theorem p13ToRotation_E23 : p13ToRotation E23 = rotationWord e23Word :=
  p13ToRotation_generator 3

@[simp] theorem p13ToRotation_E31 : p13ToRotation E31 = rotationWord e31Word :=
  p13ToRotation_generator 4

@[simp] theorem p13ToRotation_E32 : p13ToRotation E32 = rotationWord e32Word :=
  p13ToRotation_generator 5

private def p13ZPreimageFree : FreeGroup P13Generator :=
  word [(0, true), (2, false), (4, false), (0, true),
    (1, true), (4, false), (4, false), (1, true)]

private def p13XYPreimageFree : FreeGroup P13Generator :=
  word [(0, false), (1, false), (4, true)]

private theorem p13ToRotation_comp_p13Word :
    p13ToRotation.comp p13Word = rotationWord.comp p13FreeMap := by
  ext i
  change p13ToRotation (p13Word (FreeGroup.of i)) =
    rotationWord (p13FreeMap (FreeGroup.of i))
  rw [show p13Word (FreeGroup.of i) = PresentedGroup.of i by rfl,
    p13ToRotation_generator]
  simp [p13GeneratorToRotation, p13FreeMap]

private theorem p13ZPreimage_image :
    p13ToRotation (p13Word p13ZPreimageFree) = Z := by
  change (p13ToRotation.comp p13Word) p13ZPreimageFree = Z
  rw [p13ToRotation_comp_p13Word]
  apply eq_of_mul_inv_eq_one
  change rotationWord (p13FreeMap p13ZPreimageFree) *
    (rotationWord rz)⁻¹ = 1
  rw [← map_inv, ← map_mul]
  have hfree : p13FreeMap p13ZPreimageFree * rz⁻¹ =
      word (rotationSignedWord
        "YxzYXZXYXyXyZXyXYxzYzYXYXyZXyXXyZXyzYXYZ") := by
    decide
  rw [hfree]
  exact rangeZImage_eq_one

private theorem p13XYPreimage_image :
    p13ToRotation (p13Word p13XYPreimageFree) = X * Y := by
  change (p13ToRotation.comp p13Word) p13XYPreimageFree = X * Y
  rw [p13ToRotation_comp_p13Word]
  apply eq_of_mul_inv_eq_one
  change rotationWord (p13FreeMap p13XYPreimageFree) *
    (rotationWord (rx * ry))⁻¹ = 1
  rw [← map_inv, ← map_mul]
  have hfree : p13FreeMap p13XYPreimageFree * (rx * ry)⁻¹ =
      word (rotationSignedWord "xyZXyyxyZYxzYxYX") := by
    decide
  rw [hfree]
  exact rangeXYImage_eq_one

/-- The corrected short-word homomorphism is onto `Rotation`. -/
theorem p13ToRotation_surjective : Function.Surjective p13ToRotation := by
  rw [← MonoidHom.range_eq_top]
  have hclosure :
      Subgroup.closure ({Z, X * Y} : Set Rotation) ≤ p13ToRotation.range := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact ⟨p13Word p13ZPreimageFree, p13ZPreimage_image⟩
    · exact ⟨p13Word p13XYPreimageFree, p13XYPreimage_image⟩
  rw [closure_Z_XY_eq_top] at hclosure
  exact top_unique hclosure

end

end LiteralBaseP13RotationQuotient
end GroupApproximation

namespace GroupApproximation
namespace LiteralBaseP13RotationQuotient

open PresentedGroupRelatorReplay LiteralBaseP13RotationReplay
open LiteralBaseRotationRetract LiteralP13Presentation

noncomputable section

/-! ## Public word forms of the six letter images

The private short-word data above is re-exposed with explicit string
literals, so that downstream modules can evaluate the images without
access to the private definitions. -/

theorem p13ToRotation_E12_word :
    p13ToRotation E12 = rotationWord (word (rotationSignedWord "YxzYX")) :=
  p13ToRotation_generator 0

theorem p13ToRotation_E13_word :
    p13ToRotation E13 = rotationWord (word (rotationSignedWord "xzYXY")) :=
  p13ToRotation_generator 1

theorem p13ToRotation_E21_word :
    p13ToRotation E21 = rotationWord (word (rotationSignedWord "Yxyxz")) :=
  p13ToRotation_generator 2

theorem p13ToRotation_E23_word :
    p13ToRotation E23 = rotationWord (word (rotationSignedWord "XYxzY")) :=
  p13ToRotation_generator 3

theorem p13ToRotation_E31_word :
    p13ToRotation E31 = rotationWord (word (rotationSignedWord "xYxzYx")) :=
  p13ToRotation_generator 4

theorem p13ToRotation_E32_word :
    p13ToRotation E32 = rotationWord (word (rotationSignedWord "XzYXYX")) :=
  p13ToRotation_generator 5

end

end LiteralBaseP13RotationQuotient
end GroupApproximation
