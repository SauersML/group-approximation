import GroupApproximation.Leavitt.ElementaryStabilization
import GroupApproximation.PropertyT.FreeElementaryPropertyT
import GroupApproximation.PropertyTT.FreeAlgebraTranspose
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Two rank-three root geometries inside rank four

The column copy on coordinates `1,2,3` controls the last two entries of the
fourth column.  The inverse-transposed copy on coordinates `0,1,2` controls
the first row.  Their finite root directions all commute with `X₀₃`, and a
single commutator between the two planes produces any element of `X₀₃`.
-/

namespace GroupApproximation
namespace RankFourRootGeometry

open FreeElementaryPropertyT
open FreeElementaryTranspose

noncomputable section

variable (X : Type*) [Fintype X]

abbrev R := FreeAlgebra (ZMod 2) X
abbrev G3 := elementaryGroup (Fin 3) (R X)
abbrev G4 := elementaryGroup (Fin 4) (R X)

/-- The elementary rank-three block on coordinates `0,1,2`. -/
noncomputable def embed012 : G3 X →* G4 X :=
  (elementaryReindexEquiv (R := R X)
    (finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4)).toMonoidHom.comp
      (elementaryStabilization (ι := Fin 3) (κ := Fin 1) (R := R X))

/-- The elementary rank-three block on coordinates `1,2,3`. -/
noncomputable def embed123 : G3 X →* G4 X :=
  (elementaryReindexEquiv (R := R X) (finRotate 4)).toMonoidHom.comp
    (embed012 X)

/-- The inverse-transposed rank-three block on coordinates `0,1,2`; column
planes in the source become row planes in rank four. -/
noncomputable def embedRow012 : G3 X →* G4 X :=
  (embed012 X).comp
    (elementaryTransposeEquiv X (Fin 3)).toMonoidHom

omit [Fintype X] in
@[simp] theorem embed012_elementaryRoot
    (i j : Fin 3) (hij : i ≠ j) (a : R X) :
    embed012 X (elementaryRoot i j hij a) =
      elementaryRoot (Fin.castAdd 1 i) (Fin.castAdd 1 j)
        ((Fin.castAddEmb 1).injective.ne hij) a := by
  simp [embed012]
  rfl

omit [Fintype X] in
@[simp] theorem embed123_elementaryRoot
    (i j : Fin 3) (hij : i ≠ j) (a : R X) :
    embed123 X (elementaryRoot i j hij a) =
      elementaryRoot (finRotate 4 (Fin.castAdd 1 i))
        (finRotate 4 (Fin.castAdd 1 j))
        ((finRotate 4).injective.ne ((Fin.castAddEmb 1).injective.ne hij)) a := by
  simp [embed123]

/-- Word reversal fixes the unit and each free generator; in characteristic
two the sign introduced by inverse transpose also disappears. -/
theorem reverse_controlCoefficient
    (q : Option (Fin (Fintype.card X))) :
    -MulOpposite.unop (FreeAlgebra.reverseEquiv (ZMod 2) X
      (controlCoefficient X q)) = controlCoefficient X q := by
  cases q <;> simp [controlCoefficient, CharTwo.neg_eq]

omit [Fintype X] in
/-- Applying the signed word-reversal coefficient map twice is the
identity.  This is the coefficient-level surjectivity needed for arbitrary
row roots, not only the finite control coefficients. -/
theorem signedReverse_involutive (a : R X) :
    -MulOpposite.unop (FreeAlgebra.reverseEquiv (ZMod 2) X
      (-MulOpposite.unop (FreeAlgebra.reverseEquiv (ZMod 2) X a))) = a := by
  have hcoeff := FreeAlgebra.reverseHom_involutive (ZMod 2) X a
  simp [FreeAlgebra.reverseEquiv, hcoeff, CharTwo.neg_eq]

omit [Fintype X] in
/-- The inverse-transposed upper-left block sends an arbitrary source root
to the opposite row root with signed reversed coefficient. -/
theorem embedRow012_elementaryRoot
    (i j : Fin 3) (hij : i ≠ j) (a : R X) :
    embedRow012 X (elementaryRoot i j hij a) =
      elementaryRoot (Fin.castAdd 1 j) (Fin.castAdd 1 i)
        ((Fin.castAddEmb 1).injective.ne hij.symm)
        (-MulOpposite.unop (FreeAlgebra.reverseEquiv (ZMod 2) X a)) := by
  rw [show embedRow012 X (elementaryRoot i j hij a) =
      embed012 X (elementaryTransposeEquiv X (Fin 3)
        (elementaryRoot i j hij a)) from rfl]
  rw [elementaryTransposeEquiv_elementaryRoot,
    embed012_elementaryRoot]

omit [Fintype X] in
/-- Every upper-left row root has an explicit preimage under the
inverse-transposed rank-three embedding. -/
theorem embedRow012_preimage_elementaryRoot
    (i j : Fin 3) (hij : i ≠ j) (a : R X) :
    embedRow012 X
        (elementaryRoot j i hij.symm
          (-MulOpposite.unop
            (FreeAlgebra.reverseEquiv (ZMod 2) X a))) =
      elementaryRoot (Fin.castAdd 1 i) (Fin.castAdd 1 j)
        ((Fin.castAddEmb 1).injective.ne hij) a := by
  rw [embedRow012_elementaryRoot, signedReverse_involutive]

@[simp] theorem embedRow012_controlRoot
    (i j : Fin 3) (hij : i ≠ j)
    (q : Option (Fin (Fintype.card X))) :
    embedRow012 X
        (elementaryRoot i j hij (controlCoefficient X q)) =
      elementaryRoot (Fin.castAdd 1 j) (Fin.castAdd 1 i)
        ((Fin.castAddEmb 1).injective.ne hij.symm)
        (controlCoefficient X q) := by
  rw [show embedRow012 X
      (elementaryRoot i j hij (controlCoefficient X q)) =
        embed012 X (elementaryTransposeEquiv X (Fin 3)
          (elementaryRoot i j hij (controlCoefficient X q))) from rfl]
  rw [elementaryTransposeEquiv_elementaryRoot,
    reverse_controlCoefficient, embed012_elementaryRoot]

end
end RankFourRootGeometry
end GroupApproximation
