import GroupApproximation.CharClass.AcyclicModels

/-!
# Acyclicity from a contraction

`AcyclicOnModels` asks that positive-degree cycles over the models be
boundaries.  The universal source of that hypothesis is a **contraction above
degree zero**: a degreewise operator `s k : C_k ⟶ C_{k+1}` with

```text
𝟙 = d ∘ s + s ∘ d       in every positive degree.
```

Degree `0` is deliberately left unconstrained.  This is not laziness: the
singular chain complex of a contractible space is *not* contractible — its
`H₀` is the coefficient ring — and only its augmentation is.  A hypothesis
"the identity of `C` is null-homotopic" would therefore be false for every
model of the intended application, whereas the positive-degree identity above
is exactly what the augmented contraction supplies.

The file records:

* `PositiveContraction`, and `PositiveContraction.exists_preimage`, the two-line
  computation that turns it into the acyclicity hypothesis;
* `acyclicOnModels_of_contraction`, assembling a family of contractions of the
  models into `AcyclicOnModels`;
* `PositiveContraction.ofHomotopy`, extracting a contraction from a `Homotopy`
  between the identity and any chain map that vanishes in positive degrees
  (that chain map is `η ∘ ε` in the application, the augmentation composed with
  its splitting).
-/

universe u v w

namespace GroupApproximation.CharClass

open CategoryTheory CategoryTheory.Limits

variable {Λ : Type} [CommRing Λ]

/-- A **contraction above degree zero** of a chain complex of `Λ`-modules: a
degreewise operator satisfying `𝟙 = d ∘ s + s ∘ d` in every positive degree.
Degree `0` is unconstrained. -/
structure PositiveContraction (C : ChainComplex (ModuleCat.{0} Λ) ℕ) where
  /-- The contracting operator. -/
  s : ∀ k : ℕ, C.X k ⟶ C.X (k + 1)
  /-- The contraction identity, in positive degrees only. -/
  comm : ∀ k : ℕ,
    𝟙 (C.X (k + 1)) = C.d (k + 1) k ≫ s k + s (k + 1) ≫ C.d (k + 2) (k + 1)

namespace PositiveContraction

variable {C : ChainComplex (ModuleCat.{0} Λ) ℕ}

/-- A contraction above degree zero makes positive-degree cycles into
boundaries. -/
lemma exists_preimage (h : PositiveContraction C) (k : ℕ) (y : C.X (k + 1))
    (hy : (C.d (k + 1) k).hom y = 0) :
    ∃ z : C.X (k + 2), (C.d (k + 2) (k + 1)).hom z = y := by
  refine ⟨(h.s (k + 1)).hom y, ?_⟩
  have hcomm := congrArg (fun u : C.X (k + 1) ⟶ C.X (k + 1) => u.hom y) (h.comm k)
  simp only [ModuleCat.hom_id, LinearMap.id_apply, ModuleCat.hom_add, LinearMap.add_apply,
    ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
  rw [hy, map_zero, zero_add] at hcomm
  exact hcomm.symm

/-- A homotopy between the identity of `C` and a chain map that vanishes in
positive degrees is a contraction above degree zero. -/
def ofHomotopy {α : C ⟶ C} (h : Homotopy (𝟙 C) α) (hα : ∀ k : ℕ, α.f (k + 1) = 0) :
    PositiveContraction C where
  s k := h.hom k (k + 1)
  comm k := by
    have hc := h.comm (k + 1)
    rw [dNext_eq h.hom (show (ComplexShape.down ℕ).Rel (k + 1) k from rfl),
      prevD_eq h.hom (show (ComplexShape.down ℕ).Rel (k + 2) (k + 1) from rfl),
      hα k, add_zero, HomologicalComplex.id_f] at hc
    exact hc

end PositiveContraction

/-- A family of contractions of the models produces the acyclicity hypothesis of
the acyclic-models theorem. -/
lemma acyclicOnModels_of_contraction {C : Type u} [Category.{v} C] {ι : Type w}
    (M : ι → C) (G : C ⥤ ChainComplex (ModuleCat.{0} Λ) ℕ)
    (h : ∀ i : ι, PositiveContraction (G.obj (M i))) : AcyclicOnModels M Λ G where
  exists_preimage i k y hy := (h i).exists_preimage k y hy

end GroupApproximation.CharClass
