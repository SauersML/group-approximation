import GroupApproximation.Leavitt.ElementaryRoots
import Mathlib.Algebra.Group.Units.Opposite
import Mathlib.Data.Matrix.Basic

/-!
# The inverse-transpose automorphism over a free algebra

Word reversal identifies a free algebra with its opposite.  Combining this
anti-involution with matrix transpose and group inversion gives an honest
automorphism of the elementary group, interchanging row and column roots.
-/

namespace GroupApproximation

open MulOpposite

noncomputable section

universe u

namespace FreeAlgebra

variable (R : Type*) [CommRing R] (X : Type*)

/-- Reverse every noncommutative word, expressed by the universal property as
a homomorphism to the opposite algebra. -/
noncomputable def reverseHom :
    FreeAlgebra R X →ₐ[R] (FreeAlgebra R X)ᵐᵒᵖ :=
  FreeAlgebra.lift R (fun x ↦ op (FreeAlgebra.ι R x))

@[simp] theorem reverseHom_ι (x : X) :
    reverseHom R X (FreeAlgebra.ι R x) =
      op (FreeAlgebra.ι R x) := by
  simp [reverseHom]

@[simp] theorem reverseHom_algebraMap (r : R) :
    reverseHom R X (algebraMap R (FreeAlgebra R X) r) =
      algebraMap R (FreeAlgebra R X)ᵐᵒᵖ r := by
  exact (reverseHom R X).commutes r

/-- Reversing words twice is the identity. -/
theorem reverseHom_involutive (a : FreeAlgebra R X) :
    unop (reverseHom R X (unop (reverseHom R X a))) = a := by
  induction a using FreeAlgebra.induction with
  | grade0 r => simp
  | grade1 x => simp
  | mul a b ha hb => simpa using congrArg₂ (· * ·) ha hb
  | add a b ha hb => simpa using congrArg₂ (· + ·) ha hb

/-- The free algebra is canonically isomorphic to its opposite by word
reversal. -/
noncomputable def reverseEquiv :
    FreeAlgebra R X ≃ₐ[R] (FreeAlgebra R X)ᵐᵒᵖ where
  toFun := reverseHom R X
  invFun y := unop (reverseHom R X (unop y))
  left_inv := reverseHom_involutive R X
  right_inv y := by
    apply unop_injective
    exact reverseHom_involutive R X (unop y)
  map_mul' := (reverseHom R X).map_mul
  map_add' := (reverseHom R X).map_add
  commutes' := (reverseHom R X).commutes

@[simp] theorem reverseEquiv_ι (x : X) :
    reverseEquiv R X (FreeAlgebra.ι R x) =
      op (FreeAlgebra.ι R x) := by
  simp [reverseEquiv]

end FreeAlgebra

/-- Inversion identifies the opposite of a group with the group itself. -/
def oppositeGroupInvEquiv (G : Type*) [Group G] : Gᵐᵒᵖ ≃* G where
  toFun g := (unop g)⁻¹
  invFun g := op g⁻¹
  left_inv g := by simp
  right_inv g := by simp
  map_mul' g h := by simp

namespace FreeElementaryTranspose

variable (X : Type*)
abbrev R := FreeAlgebra (ZMod 2) X

/-- Coefficient reversal followed by transpose, as a ring equivalence into
the opposite matrix ring. -/
noncomputable def matrixAntiEquiv (I : Type*) [Fintype I] [DecidableEq I] :
    Matrix I I (R X) ≃+* (Matrix I I (R X))ᵐᵒᵖ :=
  (FreeAlgebra.reverseEquiv (ZMod 2) X).toRingEquiv.mapMatrix.trans
    RingEquiv.mopMatrix

/-- Inverse transpose with word reversal, on invertible matrices. -/
noncomputable def unitTransposeEquiv (I : Type*) [Fintype I] [DecidableEq I] :
    (Matrix I I (R X))ˣ ≃* (Matrix I I (R X))ˣ :=
  (Units.mapEquiv (matrixAntiEquiv X I).toMulEquiv).trans <|
    Units.opEquiv.trans (oppositeGroupInvEquiv _)

/-- The underlying entry formula for coefficient reversal and transpose. -/
@[simp] theorem unop_matrixAntiEquiv_apply
    (I : Type*) [Fintype I] [DecidableEq I]
    (M : Matrix I I (R X)) (i j : I) :
    unop (matrixAntiEquiv X I M) i j =
      unop (FreeAlgebra.reverseEquiv (ZMod 2) X (M j i)) := by
  rfl

@[simp] theorem unitTransposeEquiv_val
    (I : Type*) [Fintype I] [DecidableEq I]
    (u : (Matrix I I (R X))ˣ) :
    (unitTransposeEquiv X I u : Matrix I I (R X)) =
      unop (matrixAntiEquiv X I
        (↑(u⁻¹) : Matrix I I (R X))) := by
  let w : (Matrix I I (R X))ᵐᵒᵖˣ :=
    (Units.mapEquiv (matrixAntiEquiv X I).toMulEquiv) u
  change unop (↑(w⁻¹) : (Matrix I I (R X))ᵐᵒᵖ) =
    unop (matrixAntiEquiv X I (↑(u⁻¹) : Matrix I I (R X)))
  have h := congrArg
    (fun z : (Matrix I I (R X))ᵐᵒᵖˣ ↦
      (z : (Matrix I I (R X))ᵐᵒᵖ))
    ((Units.mapEquiv (matrixAntiEquiv X I).toMulEquiv).map_inv u)
  exact congrArg unop h.symm

/-- The inverse-transpose equivalence sends a root to the reversed opposite
root. -/
theorem unitTransposeEquiv_elementaryUnit
    (I : Type*) [Fintype I] [DecidableEq I]
    (i j : I) (hij : i ≠ j) (a : R X) :
    unitTransposeEquiv X I (elementaryUnit i j hij a) =
      elementaryUnit j i hij.symm
        (-unop (FreeAlgebra.reverseEquiv (ZMod 2) X a)) := by
  apply Units.ext
  rw [unitTransposeEquiv_val]
  ext p q
  by_cases h : i = q ∧ j = p
  · rcases h with ⟨rfl, rfl⟩
    simp [elementaryUnit, Matrix.single, hij.symm, sub_eq_add_neg]
  · have h' : ¬(j = p ∧ i = q) := by tauto
    simp [elementaryUnit, Matrix.single, h, h']

/-- Inverse transpose preserves the elementary subgroup. -/
theorem unitTransposeEquiv_elementaryGroup
    (I : Type*) [Fintype I] [DecidableEq I] :
    (elementaryGroup I (R X)).map (unitTransposeEquiv X I).toMonoidHom =
      elementaryGroup I (R X) := by
  apply le_antisymm
  · rw [elementaryGroup, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro _ ⟨i, j, hij, a, rfl⟩
    change unitTransposeEquiv X I (elementaryUnit i j hij a) ∈
      elementaryGroup I (R X)
    rw [unitTransposeEquiv_elementaryUnit]
    exact elementaryUnit_mem _ _ _ _
  · rw [elementaryGroup, Subgroup.closure_le]
    rintro _ ⟨i, j, hij, a, rfl⟩
    let a' : R X :=
      -unop (FreeAlgebra.reverseEquiv (ZMod 2) X a)
    refine ⟨elementaryUnit j i hij.symm a', elementaryUnit_mem _ _ _ _, ?_⟩
    change unitTransposeEquiv X I (elementaryUnit j i hij.symm a') =
      elementaryUnit i j hij a
    rw [unitTransposeEquiv_elementaryUnit]
    have hcoeff :
        unop (FreeAlgebra.reverseHom (ZMod 2) X
          (unop (FreeAlgebra.reverseHom (ZMod 2) X a))) = a :=
      FreeAlgebra.reverseHom_involutive (ZMod 2) X a
    simp [a', FreeAlgebra.reverseEquiv, hcoeff]

/-- Inverse transpose as an automorphism of the elementary group. -/
noncomputable def elementaryTransposeEquiv
    (I : Type*) [Fintype I] [DecidableEq I] :
    elementaryGroup I (R X) ≃* elementaryGroup I (R X) :=
  ((unitTransposeEquiv X I).subgroupMap (elementaryGroup I (R X))).trans
    (MulEquiv.subgroupCongr (unitTransposeEquiv_elementaryGroup X I))

/-- Root formula inside the elementary group. -/
theorem elementaryTransposeEquiv_elementaryRoot
    (I : Type*) [Fintype I] [DecidableEq I]
    (i j : I) (hij : i ≠ j) (a : R X) :
    elementaryTransposeEquiv X I (elementaryRoot i j hij a) =
      elementaryRoot j i hij.symm
        (-unop (FreeAlgebra.reverseEquiv (ZMod 2) X a)) := by
  apply Subtype.ext
  exact unitTransposeEquiv_elementaryUnit X I i j hij a

end FreeElementaryTranspose

end
end GroupApproximation
