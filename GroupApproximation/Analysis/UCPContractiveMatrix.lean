import GroupApproximation.Analysis.CStarFormCompletelyPositive
import GroupApproximation.Analysis.CStarUnitalCPContractive
import GroupApproximation.Analysis.LanceMatrixArveson
import GroupApproximation.Analysis.NaturalMatrixCoordinateEquiv
import GroupApproximation.Analysis.QuasidiagonalTrace

/-!
# The last mile: a ucp map into `M_Y` is a contraction

`Quasidiagonal.UCPContractive` is what is left of the typed input the
quasidiagonal-trace route used to carry.  Its `⋆`-preservation companion became
`Quasidiagonal.ucp_map_star`; this file discharges the survivor, and with it the
whole input.

Nothing here is a theorem about C⋆-algebras.  Every mathematical step already
exists:

* `CStarExactness.isCompletelyPositive_of_form` --- form positivity plus
  `⋆`-preservation gives complete positivity, at `B(ℂᵏ)`;
* `CStarExactness.IsCompletelyPositive.norm_apply_le_of_unital` --- a unital
  completely positive map into bounded operators is a contraction, off the
  repository's Stinespring dilation;
* `Quasidiagonal.ucp_map_star` --- the `⋆`-preservation those two need.

What this file supplies is the change of coordinates between them, in two
moves, neither of which is a theorem anyone cites.

## The two moves

`Matrix Y Y ℂ` for `Y : FiniteModel` is not `B(ℂᵏ)`, for two unrelated reasons:
the index set is not `Fin k`, and matrices are not operators.  Both are handled
by maps this repository already has and both are isometric:

* `matrixReindexStarAlgEquiv` at
  `Fintype.equivFin Y`, with `norm_matrixReindexStarAlgEquiv`;
* `Matrix.toEuclideanCLM`, with `Matrix.l2_opNorm_toEuclideanCLM` --- the
  scoped `Matrix.Norms.L2Operator` structure *is* the operator norm pulled back
  along it, so this is definitional rather than a theorem.

`euclideanize` is the composite, and `norm_euclideanize` is that it changes no
norms.

## Status

**The statement of `ucp_norm_le` did not elaborate on its first run**, for a
reason worth recording: the operator norm on `Matrix Y Y ℂ` is a *scoped*
instance (`Matrix.Norms.L2Operator`), so `‖M‖` fails to synthesize in a module
that does not open it, and every declaration after the failure is reported as
using `sorry` with no `sorry` in the source.  The `open scoped` line above is
that fix; the proof body below has therefore been checked only by reading, and
wants one compile before it is trusted.

## The form, in two vocabularies

`Quasidiagonal.IsCompletelyPositiveOnMatrices` is stated entrywise,
`CStarExactness.isCompletelyPositive_of_form` on inner products.  They agree on
the nose: `CStarExactness.inner_toEuclideanCLM_expand` says

```text
    ⟪u, toEuclideanCLM M w⟫ = ∑ₚ ∑_q conj (u p) * (M p q * w q),
```

and reindexing the two sums along `Fintype.equivFin Y` turns the vectors
`v : Fin k → ℂ` into the vectors `w x = v (e x)` the entrywise condition
quantifies over.  The only friction is associativity: one side brackets
`conj u * M * w`, the other `conj u * (M * w)`.
-/

namespace GroupApproximation
namespace Quasidiagonal

open scoped InnerProductSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-! ## Matrices over a finite model, as operators on `ℓ²` -/

/-- The canonical enumeration of a finite model.  Named rather than written
inline so that every occurrence is the same term: `rw` matches syntactically,
and `Fintype.equivFin Y` appearing in one place and an abbreviation in another
is the difference between a rewrite that fires and one that does not. -/
def enum (Y : FiniteModel) : Y ≃ Fin (Fintype.card Y) := Fintype.equivFin Y

/-- Reindex to `Fin (card Y)` and view the result as an operator.  Both halves
are `⋆`-algebra equivalences, so the composite is linear. -/
def euclideanize (Y : FiniteModel) :
    Matrix Y Y ℂ →ₗ[ℂ] (EuclideanSpace ℂ (Fin (Fintype.card Y)) →L[ℂ]
      EuclideanSpace ℂ (Fin (Fintype.card Y))) where
  toFun M := Matrix.toEuclideanCLM (𝕜 := ℂ)
    (matrixReindexStarAlgEquiv
      (enum Y) M)
  map_add' M N := by simp
  map_smul' c M := by simp

@[simp] theorem euclideanize_apply (Y : FiniteModel) (M : Matrix Y Y ℂ) :
    euclideanize Y M = Matrix.toEuclideanCLM (𝕜 := ℂ)
      (matrixReindexStarAlgEquiv
        (enum Y) M) := rfl

/-- **Neither move changes a norm.** -/
theorem norm_euclideanize (Y : FiniteModel) (M : Matrix Y Y ℂ) :
    ‖euclideanize Y M‖ = ‖M‖ := by
  rw [euclideanize_apply, Matrix.l2_opNorm_toEuclideanCLM,
    norm_matrixReindexStarAlgEquiv]

theorem euclideanize_one (Y : FiniteModel) : euclideanize Y 1 = 1 := by
  rw [euclideanize_apply, map_one, map_one]

theorem euclideanize_star (Y : FiniteModel) (M : Matrix Y Y ℂ) :
    euclideanize Y (star M) = star (euclideanize Y M) := by
  rw [euclideanize_apply, euclideanize_apply, map_star, map_star]

/-! ## The bound -/

/-- **A unital completely positive map into `M_Y` is a contraction.**  This is
the surviving clause of `UCPContractive`, proved. -/
theorem ucp_norm_le {Y : FiniteModel} (φ : A →ₗ[ℂ] Matrix Y Y ℂ)
    (h1 : φ 1 = 1) (hcp : IsCompletelyPositiveOnMatrices Y ⇑φ) (b : A) :
    ‖φ b‖ ≤ ‖b‖ := by
  classical
  set ψ : A →ₗ[ℂ] (EuclideanSpace ℂ (Fin (Fintype.card Y)) →L[ℂ]
      EuclideanSpace ℂ (Fin (Fintype.card Y))) :=
    (euclideanize Y).comp φ with hψ
  have hψ1 : ψ 1 = 1 := by
    rw [hψ, LinearMap.comp_apply, h1, euclideanize_one]
  have hψstar : ∀ c : A, ψ (star c) = star (ψ c) := by
    intro c
    rw [hψ, LinearMap.comp_apply, LinearMap.comp_apply,
      ucp_map_star φ h1 hcp c, ← Matrix.star_eq_conjTranspose,
      euclideanize_star]
  have hψform : ∀ (m : ℕ) (a : Fin m → A)
      (v : Fin m → EuclideanSpace ℂ (Fin (Fintype.card Y))),
      0 ≤ (∑ i : Fin m, ∑ j : Fin m,
        ⟪v i, ψ (star (a i) * a j) (v j)⟫_ℂ).re := by
    intro m a v
    have hentry : ∀ i j : Fin m,
        ⟪v i, ψ (star (a i) * a j) (v j)⟫_ℂ
          = ∑ x : Y, ∑ y : Y, (starRingEnd ℂ) (v i (enum Y x))
              * (φ (star (a i) * a j) x y * v j (enum Y y)) := by
      intro i j
      rw [hψ, LinearMap.comp_apply, euclideanize_apply,
        CStarExactness.inner_toEuclideanCLM_expand]
      -- both index sets are the same set, enumerated; `Fintype.sum_equiv`
      -- transports without asking the goal to match a written-out lambda
      symm
      refine Fintype.sum_equiv (enum Y) _ _ fun x ↦ ?_
      refine Fintype.sum_equiv (enum Y) _ _ fun y ↦ ?_
      congr 2
      simp [matrixReindexStarAlgEquiv]
    rw [Finset.sum_congr rfl fun i _ ↦
      Finset.sum_congr rfl fun j _ ↦ hentry i j]
    have hassoc : ∀ i j : Fin m,
        (∑ x : Y, ∑ y : Y, (starRingEnd ℂ) (v i (enum Y x))
            * (φ (star (a i) * a j) x y * v j (enum Y y)))
          = ∑ x : Y, ∑ y : Y, (starRingEnd ℂ) (v i (enum Y x))
              * φ (star (a i) * a j) x y * v j (enum Y y) := by
      intro i j
      refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
      rw [mul_assoc]
    rw [Finset.sum_congr rfl fun i _ ↦
      Finset.sum_congr rfl fun j _ ↦ hassoc i j]
    exact (hcp m a (fun i x ↦ v i (enum Y x))).2
  have hCP : CStarExactness.IsCompletelyPositive ψ :=
    CStarExactness.isCompletelyPositive_of_form ψ hψstar hψform
  have hbound := hCP.norm_apply_le_of_unital hψ1 b
  rwa [hψ, LinearMap.comp_apply, norm_euclideanize] at hbound

/-- **The input, discharged.**  `UCPContractive` is inhabited. -/
theorem ucpContractive : UCPContractive.{u} :=
  ⟨fun _ _ _ φ h1 hcp b ↦ ucp_norm_le φ h1 hcp b⟩

end

end Quasidiagonal
end GroupApproximation
