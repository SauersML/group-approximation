/-
Local adaptation of the HamSandwich development at
https://github.com/akopjan/HamSandwich/tree/76202dbbb6610ffcebbccfbf7a56f833a4c2a376
Changed for this repository: namespace isolation, Lean 4.32 porting,
and local proof integration. The original license is retained in this tree.
-/
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SingularCohomology
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

























































open CategoryTheory MonoidalCategory Limits

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## 1. Coefficient-category wiring (gap `U6`)

The chain/cochain monoidal structure on `HomologicalComplex C c` requires the
additivity of `curriedTensor C` both in its argument object and as a functor.
Both follow from `MonoidalPreadditive C` but are not registered upstream. -/

/-! ## 2. Tensor signs for the cochain shape `ComplexShape.up ℕ`

Mathlib registers `TensorSigns` for `down ℕ` and `up ℤ`, but not for `up ℕ`, the
shape of the singular cochain complex. We supply it with the same `(-1)^•`
convention as the chain case. -/

/- The `ComplexShape.TensorSigns` instance for the cochain shape
`ComplexShape.up ℕ`, using the sign `ε n = (-1)^n`. This is the missing piece
that makes `HomologicalComplex.monoidalCategory` apply to
`CochainComplex (ModuleCat R) ℕ`. -/
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance tensorSigns_up_nat : (ComplexShape.up ℕ).TensorSigns where
  ε' := MonoidHom.mk' (fun (i : ℕ) => (-1 : ℤˣ) ^ i) (pow_add (-1 : ℤˣ))
  rel_add p q r (hpq : p + 1 = q) := by dsimp; lia
  add_rel p q r (hpq : p + 1 = q) := by dsimp; lia
  ε'_succ := by rintro p _ rfl; dsimp; rw [pow_add, pow_one, mul_neg, mul_one]

/-- The Koszul sign of `ComplexShape.up ℕ` at index `n` is `(-1)^n`. -/
@[simp]
theorem ε_up_nat (n : ℕ) : (ComplexShape.up ℕ).ε n = (-1 : ℤˣ) ^ n := rfl

/-! ## 3. The singular cochain tensor square `C^•(X) ⊗ C^•(X)`

With the wiring of §1–§2 in place, the tensor product of the singular cochain
complex with itself is a genuine cochain complex, functorial in `X`. This is the
domain of a future cup product (a map `C^•(X) ⊗ C^•(X) → C^•(X)`), and its
functorial pullback is the naturality substrate for `f^*(a ⌣ b) = f^* a ⌣ f^* b`. -/

/-- The **tensor square of the singular cochain complex** with coefficients in
`M : ModuleCat R`, i.e. `C^•(X; M) ⊗ C^•(X; M)` as a `CochainComplex (ModuleCat R) ℕ`.
This is the cochain-level domain of a cup product `⌣ : C^•(X) ⊗ C^•(X) → C^•(X)`. -/
noncomputable def singularCochainTensorSquare (R : Type) [CommRing R]
    (M : ModuleCat.{0} R) (X : TopCat.{0}ᵒᵖ) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  MonoidalCategory.tensorObj ((singularCochainComplexFunctor R M).obj X)
    ((singularCochainComplexFunctor R M).obj X)

/-- The functorial pullback on the cochain tensor square: a continuous map
(packaged as `f : X ⟶ Y` in `TopCatᵒᵖ`) induces `f^* ⊗ f^*` on the tensor
squares. This is `MonoidalCategory.tensorHom` applied to the cochain pullback
`(singularCochainComplexFunctor R M).map f` with itself. -/
noncomputable def singularCochainTensorSquareMap (R : Type) [CommRing R]
    (M : ModuleCat.{0} R) {X Y : TopCat.{0}ᵒᵖ} (f : X ⟶ Y) :
    singularCochainTensorSquare R M X ⟶ singularCochainTensorSquare R M Y :=
  MonoidalCategory.tensorHom ((singularCochainComplexFunctor R M).map f)
    ((singularCochainComplexFunctor R M).map f)

/-- Functoriality: the cochain tensor-square pullback preserves identities. -/
@[simp]
theorem singularCochainTensorSquareMap_id (R : Type) [CommRing R]
    (M : ModuleCat.{0} R) (X : TopCat.{0}ᵒᵖ) :
    singularCochainTensorSquareMap R M (𝟙 X) = 𝟙 _ := by
  rw [singularCochainTensorSquareMap, (singularCochainComplexFunctor R M).map_id]
  exact MonoidalCategory.id_tensorHom_id _ _

/-- Functoriality: the cochain tensor-square pullback preserves composition. -/
theorem singularCochainTensorSquareMap_comp (R : Type) [CommRing R]
    (M : ModuleCat.{0} R) {X Y Z : TopCat.{0}ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    singularCochainTensorSquareMap R M (f ≫ g)
      = singularCochainTensorSquareMap R M f ≫ singularCochainTensorSquareMap R M g := by
  rw [singularCochainTensorSquareMap, singularCochainTensorSquareMap,
    singularCochainTensorSquareMap, (singularCochainComplexFunctor R M).map_comp,
    ← MonoidalCategory.tensorHom_comp_tensorHom]
  rfl

/-! ## 4. `ZMod 2` specializations

The downstream `RPⁿ` work uses `ZMod 2` coefficients, where the Koszul sign is
trivial (`-1 = 1`). These are thin abbreviations of the general definitions. -/

/-- The tensor square of the singular `F₂`-cochain complex,
`C^•(X; F₂) ⊗ C^•(X; F₂)`. -/
noncomputable abbrev singularCochainTensorSquareZMod2 (X : TopCat.{0}ᵒᵖ) :
    CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  singularCochainTensorSquare (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) X

/-- The functorial pullback on the `F₂`-cochain tensor square. -/
noncomputable abbrev singularCochainTensorSquareZMod2Map {X Y : TopCat.{0}ᵒᵖ}
    (f : X ⟶ Y) :
    singularCochainTensorSquareZMod2 X ⟶ singularCochainTensorSquareZMod2 Y :=
  singularCochainTensorSquareMap (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) f

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
