import GroupApproximation.CharClass.AcyclicModels
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Acyclicity on models from vanishing homology

`AcyclicOnModels` is stated with elements — a positive-degree cycle over a model
is a boundary — because that is the form the comparison induction consumes.  In
practice what one *has* is the vanishing of a homology object: the singular
chain complex of a contractible space has `Hₖ = 0` for `k ≥ 1`, and that is
available from Mathlib through a homotopy equivalence with a point.

This file is the bridge.  For complexes of modules the passage is a single
Mathlib lemma in each direction: `HomologicalComplex.exactAt_iff_isZero_homology`
turns the vanishing into exactness of the three-term complex
`Kₖ₊₂ → Kₖ₊₁ → Kₖ`, and `ShortComplex.moduleCat_exact_iff` reads that exactness
off on elements.  `HomologicalComplex.exactAt_iff'` is used rather than
`exactAt_iff` so that the short complex is built from `K.d` at literal indices,
with no `xPrev`/`xNext` transport.
-/

universe u v w

namespace GroupApproximation.CharClass

open CategoryTheory CategoryTheory.Limits

variable {Λ : Type} [CommRing Λ]

/-- Vanishing homology in a positive degree makes cycles into boundaries. -/
lemma exists_preimage_of_isZero_homology (K : ChainComplex (ModuleCat.{0} Λ) ℕ) (k : ℕ)
    (h : IsZero (K.homology (k + 1))) (y : K.X (k + 1))
    (hy : (K.d (k + 1) k).hom y = 0) :
    ∃ z : K.X (k + 2), (K.d (k + 2) (k + 1)).hom z = y := by
  have hprev : (ComplexShape.down ℕ).prev (k + 1) = k + 2 := ChainComplex.prev ℕ (k + 1)
  have hnext : (ComplexShape.down ℕ).next (k + 1) = k := ChainComplex.next_nat_succ k
  have hex : K.ExactAt (k + 1) :=
    (HomologicalComplex.exactAt_iff_isZero_homology K (k + 1)).2 h
  rw [HomologicalComplex.exactAt_iff' (K := K) (i := k + 2) (j := k + 1) (k := k)
      hprev hnext, ShortComplex.moduleCat_exact_iff] at hex
  exact hex y hy

/-- A family of models whose complexes have vanishing positive-degree homology
gives the acyclicity hypothesis of the acyclic-models theorem. -/
lemma acyclicOnModels_of_isZero_homology {C : Type u} [Category.{v} C] {ι : Type w}
    (M : ι → C) (G : C ⥤ ChainComplex (ModuleCat.{0} Λ) ℕ)
    (h : ∀ (i : ι) (k : ℕ), IsZero ((G.obj (M i)).homology (k + 1))) :
    AcyclicOnModels M Λ G where
  exists_preimage i k y hy :=
    exists_preimage_of_isZero_homology (G.obj (M i)) k (h i k) y hy

end GroupApproximation.CharClass
