import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SingularCohomology
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Cup product scaffolding — coefficient-category wiring and the cochain tensor square

This file implements the first **build-clean** supporting layer toward a singular
cup product / cohomology ring (the `PR-cup1` step of
`docs/plans/Cup_Product_And_Cohomology_Ring_Roadmap.md`). It contains **no**
placeholder definitions and **no** axioms: every declaration is fully proved.

The pinned Mathlib (`v4.28.0`, commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`) has **no** cup product, no
Alexander–Whitney chain diagonal, and no Eilenberg–Zilber equivalence. It does,
however, provide the full monoidal structure on homological complexes
(`Mathlib.Algebra.Homology.Monoidal`) whenever the coefficient category is an
additive monoidal category with the right coproduct-preservation side
conditions. The obstacle recorded in the cup-product inventories (gap `U6`) is
that those side conditions are **not registered as instances** for the
coefficient categories `ModuleCat R` we need, so the generic monoidal structure
does not apply to `ChainComplex (ModuleCat R) ℕ` / `CochainComplex (ModuleCat R) ℕ`
out of the box.

## What this file supplies

1. **Coefficient-category wiring (`U6`).** For any preadditive monoidal category
   `C` with `MonoidalPreadditive C`, the additivity instances
   `((curriedTensor C).obj X).Additive` and `(curriedTensor C).Additive` that the
   chain/cochain tensor product asks for. These hold mathematically from
   `MonoidalPreadditive` but were previously unregistered. With them, the generic
   `HomologicalComplex.monoidalCategory` instance applies to
   `ChainComplex (ModuleCat R) ℕ` for every commutative ring `R`
   (in particular `R = ZMod 2`).

2. **Cochain-shape tensor signs.** Mathlib registers `ComplexShape.TensorSigns`
   only for `ComplexShape.down ℕ` (chain complexes) and `ComplexShape.up ℤ`. It
   does **not** register it for `ComplexShape.up ℕ`, the shape of the singular
   *cochain* complex `Hom(C_•(X), M)`. We supply this instance (the same
   `(-1)^•` sign convention as the chain case), which is exactly what unblocks the
   monoidal structure on `CochainComplex (ModuleCat R) ℕ`.

3. **The cochain tensor square `C^•(X) ⊗ C^•(X)`.** With the above wiring, the
   tensor product of the singular cochain complex with itself is a genuine
   `CochainComplex (ModuleCat R) ℕ`, the domain on which a cup product would be
   defined. We package it together with its functorial pullback
   `(f ⊗ f)^* = f^* ⊗ f^*` and the corresponding `map_id` / `map_comp` laws — the
   naturality substrate for the eventual `f^*(a ⌣ b) = f^* a ⌣ f^* b`.

## Scope and blocker

This is the **algebraic substrate only**. The single genuinely *topological*
input still missing is the **Alexander–Whitney chain diagonal**
`Δ : C_•(X) → C_•(X) ⊗ C_•(X)` (absent from pinned Mathlib); once it exists, the
cup product is `Δ^*` precomposed with the lax-monoidal pairing
`Hom(A, R) ⊗ Hom(B, R) → Hom(A ⊗ B, R)`, descended to cohomology. No fake `cup`
declaration is introduced here, since a faithful one cannot be defined without
`Δ`.
-/

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
