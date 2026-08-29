import GroupApproximation.Analysis.CStarMatrixTwoByTwo
import GroupApproximation.Analysis.ShulmanFillNormingProductMF

/-!
# `M₂` of a matrix algebra is a matrix algebra

`Analysis/ShulmanFillNormingProductMF` proves that a bounded product of matrix
algebras is MF-embeddable, and `Analysis/ShulmanFillNormingDoubledData` doubles
Shulman's models to `M₂(A n)`.  At the printed models `A n = M_{Yₙ}` the two
meet only after the doubled models are recognised as matrix algebras again:

    `M₂(M_Y) ≅ M_{Fin 2 × Y}` ,   `X ↦ fun p q ↦ X p.1 q.1 p.2 q.2` .

Mathlib has this flattening as `Matrix.comp` / `Matrix.compAlgEquiv`, but the
map is written out by hand here: its entries are unambiguous, so every clause
is an entrywise identity, and nothing rests on the exact shape of the library
equivalence.  Only injectivity is needed downstream — `HasMFEmbedding` passes
backward along any injective `*`-homomorphism — so the C-star norms never have
to be compared.

The two order instances are local, as in `Analysis/CStarMatrixTwo`: Mathlib
builds `CStarAlgebra (CStarMatrix I I K)` from the positivity order of `K`, and
this repository does not make that order global.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped Matrix.Norms.L2Operator

noncomputable section

section Flatten

/-- The doubled finite model `Fin 2 × Y`.  Named `flatDoubleModel` because
`Sofic/HyperlinearAmplification.doubleModel` already means `Y × Y`. -/
def flatDoubleModel (Y : FiniteModel) : FiniteModel :=
  ⟨Fin 2 × Y, inferInstance, inferInstance⟩

instance nonempty_flatDoubleModel (Y : FiniteModel) [Nonempty Y] :
    Nonempty (flatDoubleModel Y) :=
  inferInstanceAs (Nonempty (Fin 2 × Y))

variable (Y : FiniteModel) [Nonempty Y]

noncomputable local instance matrixCStarAlgebraForFlatten :
    CStarAlgebra (Matrix Y Y ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

noncomputable local instance partialOrderMatrixForFlatten :
    PartialOrder (Matrix Y Y ℂ) :=
  CStarAlgebra.spectralOrder (Matrix Y Y ℂ)

local instance starOrderedRingMatrixForFlatten :
    StarOrderedRing (Matrix Y Y ℂ) :=
  CStarAlgebra.spectralOrderedRing (Matrix Y Y ℂ)

/-- **Flattening a two-by-two matrix of matrices.** -/
def flattenHom :
    CStarMatrix (Fin 2) (Fin 2) (Matrix Y Y ℂ) →⋆ₐ[ℂ]
      Matrix (flatDoubleModel Y) (flatDoubleModel Y) ℂ where
  toFun X := fun p q ↦ X p.1 q.1 p.2 q.2
  map_one' := by
    ext p q
    by_cases h1 : p.1 = q.1
    · by_cases h2 : p.2 = q.2
      · have hpq : p = q := Prod.ext h1 h2
        rw [hpq]
        simp [CStarMatrix.one_apply_eq]
      · have hpq : p ≠ q := fun h ↦ h2 (congrArg Prod.snd h)
        rw [h1, CStarMatrix.one_apply_eq, Matrix.one_apply_ne h2,
          Matrix.one_apply_ne hpq]
    · have hpq : p ≠ q := fun h ↦ h1 (congrArg Prod.fst h)
      rw [CStarMatrix.one_apply_ne h1,
        Matrix.zero_apply, Matrix.one_apply_ne hpq]
  map_mul' X Z := by
    ext p q
    show (X * Z) p.1 q.1 p.2 q.2 = _
    rw [CStarMatrix.mul_apply, Matrix.sum_apply, Matrix.mul_apply]
    have hL : ∑ k : Fin 2, (X p.1 k * Z k q.1) p.2 q.2 =
        ∑ k : Fin 2, ∑ m : Y, X p.1 k p.2 m * Z k q.1 m q.2 := by
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Matrix.mul_apply]
    have hR : ∑ j : Fin 2 × Y,
        X p.1 j.1 p.2 j.2 * Z j.1 q.1 j.2 q.2
        = ∑ k : Fin 2, ∑ m : Y, X p.1 k p.2 m * Z k q.1 m q.2 :=
      Fintype.sum_prod_type' (fun k m ↦ X p.1 k p.2 m * Z k q.1 m q.2)
    rw [hL]
    exact hR.symm
  map_zero' := by
    ext p q
    show (0 : CStarMatrix (Fin 2) (Fin 2) (Matrix Y Y ℂ)) p.1 q.1 p.2 q.2 = _
    rw [CStarMatrix.zero_apply, Matrix.zero_apply, Matrix.zero_apply]
  map_add' X Z := by
    ext p q
    show (X + Z) p.1 q.1 p.2 q.2 = _
    rw [CStarMatrix.add_apply, Matrix.add_apply, Matrix.add_apply]
  commutes' z := by
    ext p q
    show (algebraMap ℂ (CStarMatrix (Fin 2) (Fin 2) (Matrix Y Y ℂ)) z)
      p.1 q.1 p.2 q.2 = _
    by_cases h1 : p.1 = q.1
    · by_cases h2 : p.2 = q.2
      · have hpq : p = q := Prod.ext h1 h2
        rw [hpq]
        simp [Algebra.algebraMap_eq_smul_one, CStarMatrix.smul_apply,
          CStarMatrix.one_apply_eq, Matrix.smul_apply]
      · have hpq : p ≠ q := fun h ↦ h2 (congrArg Prod.snd h)
        simp [Algebra.algebraMap_eq_smul_one, CStarMatrix.smul_apply, h1,
          Matrix.one_apply_ne h2, Matrix.one_apply_ne hpq, Matrix.smul_apply]
    · have hpq : p ≠ q := fun h ↦ h1 (congrArg Prod.fst h)
      simp [Algebra.algebraMap_eq_smul_one, CStarMatrix.smul_apply,
        CStarMatrix.one_apply_ne h1, Matrix.zero_apply,
        Matrix.one_apply_ne hpq, Matrix.smul_apply]
  map_star' X := by
    ext p q
    show (star X) p.1 q.1 p.2 q.2 = _
    rw [CStarMatrix.star_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply]

omit [Nonempty Y] in
@[simp] theorem flattenHom_apply
    (X : CStarMatrix (Fin 2) (Fin 2) (Matrix Y Y ℂ))
    (p q : flatDoubleModel Y) :
    flattenHom Y X p q = X p.1 q.1 p.2 q.2 := rfl

omit [Nonempty Y] in
/-- **The flattening is faithful.**  Two doubled matrices with the same
flattening agree entry by entry. -/
theorem flattenHom_injective : Function.Injective (flattenHom Y) := by
  intro X Z h
  ext i j a b
  exact congrFun (congrFun h (i, a)) (j, b)

end Flatten

end

end ShulmanFill
end GroupApproximation
