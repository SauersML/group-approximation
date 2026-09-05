import GroupApproximation.CharClass.AcyclicModelsContraction
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Tensor products of chain complexes, and acyclicity of a tensor product

The Cartan formula compares two natural equivariant chain maps whose target is a
*tensor product* of singular chain complexes, so the acyclicity hypothesis of the
acyclic-models theorem has to be checked for a tensor product.  This file does
that, once and for all, in the only form it is ever needed:

> if the identity of `C` is chain homotopic to a map vanishing in positive
> degrees, and likewise for `D`, then the same is true of `C ⊗ D`, so `C ⊗ D` is
> acyclic in positive degrees.

The hypothesis is exactly what a contractible space supplies: for `C = S(Δ^n)`
the identity is homotopic to `η ∘ ε`, the augmentation followed by its splitting,
which is concentrated in degree `0`.  Note that the identity of `S(Δ^n)` is
*not* null-homotopic — the complex has `H₀ = Λ` — which is why the hypothesis is
stated with a comparison map `α` rather than with `0`.

The tensor product used is Mathlib's `HomologicalComplex.mapBifunctor` for the
tensor bifunctor of `ModuleCat Λ`, i.e. `(C ⊗ D)_n = ⨁_{p+q=n} C_p ⊗ D_q` with
the usual total differential.  Working with `mapBifunctor` rather than with the
monoidal-category notation keeps the proof one layer away from the transported
monoidal structure, and gives direct access to the summand inclusions, which is
what the vanishing statement needs.
-/

universe u v w

namespace GroupApproximation.CharClass

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {Λ : Type} [CommRing Λ]

/-- The tensor product of two `ℕ`-graded chain complexes of `Λ`-modules:
`(C ⊗ D)_n = ⨁_{p+q=n} C_p ⊗ D_q`. -/
noncomputable abbrev tensorCx (C D : ChainComplex (ModuleCat.{0} Λ) ℕ) :
    ChainComplex (ModuleCat.{0} Λ) ℕ :=
  HomologicalComplex.mapBifunctor C D (curriedTensor (ModuleCat.{0} Λ)) (ComplexShape.down ℕ)

/-- The tensor product of two chain maps. -/
noncomputable abbrev tensorCxMap {C C' D D' : ChainComplex (ModuleCat.{0} Λ) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') : tensorCx C D ⟶ tensorCx C' D' :=
  HomologicalComplex.mapBifunctorMap f g (curriedTensor (ModuleCat.{0} Λ))
    (ComplexShape.down ℕ)

/-- Tensoring identities gives the identity. -/
lemma tensorCxMap_id (C D : ChainComplex (ModuleCat.{0} Λ) ℕ) :
    tensorCxMap (𝟙 C) (𝟙 D) = 𝟙 (tensorCx C D) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i₁ i₂ h
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp

/-- Tensoring is compatible with chain homotopies in each variable. -/
noncomputable def tensorCxHomotopy {C C' D D' : ChainComplex (ModuleCat.{0} Λ) ℕ}
    {f f' : C ⟶ C'} {g g' : D ⟶ D'} (hf : Homotopy f f') (hg : Homotopy g g') :
    Homotopy (tensorCxMap f g) (tensorCxMap f' g') :=
  (HomologicalComplex.mapBifunctorMapHomotopy₁ hf g
      (curriedTensor (ModuleCat.{0} Λ)) (ComplexShape.down ℕ)).trans
    (HomologicalComplex.mapBifunctorMapHomotopy₂ f' hg
      (curriedTensor (ModuleCat.{0} Λ)) (ComplexShape.down ℕ))

/-- The tensor product of two chain maps that vanish in positive degrees vanishes
in positive degrees: every summand `C_p ⊗ D_q` of degree `p + q ≥ 1` has one of
its two factors in a positive degree. -/
lemma tensorCxMap_f_eq_zero {C D : ChainComplex (ModuleCat.{0} Λ) ℕ} (α : C ⟶ C)
    (β : D ⟶ D) (hα : ∀ k : ℕ, α.f (k + 1) = 0) (hβ : ∀ k : ℕ, β.f (k + 1) = 0) (k : ℕ) :
    (tensorCxMap α β).f (k + 1) = 0 := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i₁ i₂ h
  have h' : i₁ + i₂ = k + 1 := h
  rw [HomologicalComplex.ι_mapBifunctorMap, comp_zero]
  rcases i₁ with _ | p
  · obtain ⟨j, rfl⟩ : ∃ j, i₂ = j + 1 := ⟨k, by omega⟩
    rw [hβ j]
    simp
  · rw [hα p]
    simp

/-- **Acyclicity of a tensor product.**  If the identity of `C` is homotopic to a
chain map vanishing in positive degrees, and likewise for `D`, then the tensor
product has a contraction above degree zero. -/
noncomputable def tensorPositiveContraction {C D : ChainComplex (ModuleCat.{0} Λ) ℕ}
    {α : C ⟶ C} {β : D ⟶ D} (hC : Homotopy (𝟙 C) α) (hD : Homotopy (𝟙 D) β)
    (hα : ∀ k : ℕ, α.f (k + 1) = 0) (hβ : ∀ k : ℕ, β.f (k + 1) = 0) :
    PositiveContraction (tensorCx C D) :=
  PositiveContraction.ofHomotopy
    ((Homotopy.ofEq (tensorCxMap_id C D).symm).trans (tensorCxHomotopy hC hD))
    (tensorCxMap_f_eq_zero α β hα hβ)

/-- Positive-degree cycles in a tensor product of contractible-up-to-degree-zero
complexes are boundaries. -/
theorem tensorCx_exists_preimage {C D : ChainComplex (ModuleCat.{0} Λ) ℕ}
    {α : C ⟶ C} {β : D ⟶ D} (hC : Homotopy (𝟙 C) α) (hD : Homotopy (𝟙 D) β)
    (hα : ∀ k : ℕ, α.f (k + 1) = 0) (hβ : ∀ k : ℕ, β.f (k + 1) = 0)
    (k : ℕ) (y : (tensorCx C D).X (k + 1))
    (hy : ((tensorCx C D).d (k + 1) k).hom y = 0) :
    ∃ z : (tensorCx C D).X (k + 2), ((tensorCx C D).d (k + 2) (k + 1)).hom z = y :=
  (tensorPositiveContraction hC hD hα hβ).exists_preimage k y hy

end GroupApproximation.CharClass
