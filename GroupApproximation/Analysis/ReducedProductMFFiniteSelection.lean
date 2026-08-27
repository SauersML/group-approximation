import GroupApproximation.Analysis.ReducedProductMFDiagonalData

/-!
# Finite simultaneous limsup selection for reduced-product MF models

At outer stage `n`, the manuscript considers the first `n+1` rational star
polynomials.  Their inner coordinate norms are eventually bounded above by
the corresponding `B_n` norms plus `1/(n+1)`.  Since each limsup equals its
`B_n` norm, every polynomial also has a designated coordinate beyond the
common threshold where its lower bound is attained.  This file makes that
finite selection explicit.
-/

namespace GroupApproximation
namespace ReducedProductMFFiniteSelection

open Filter
open PolarLiftingGeneralCStar
open RationalNoncommutativeStarPolynomial
open ReducedProductMFDiagonalData
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u v

noncomputable local instance matrixBlockCStarAlgebraForFiniteSelection
    (Z : Type*) [Fintype Z] [DecidableEq Z] [Nonempty Z] :
    CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

noncomputable local instance boundedMatrixSequenceCStarAlgebraForFiniteSelection
    (X : ℕ → Type*) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
    [∀ n, Nonempty (X n)] : CStarAlgebra (BoundedMatrixSequence X) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

variable (B : ℕ → Type u) [∀ n, CStarAlgebra (B n)]
  [∀ n, Nontrivial (B n)]
variable {C : Type v} [CStarAlgebra C]
variable (i : C →⋆ₙₐ[ℂ] CStarProductCorona B cofinite)
variable (a : ℕ → C)
variable (hB : ∀ n, HasMFEmbedding (B n))

/-- The positive error used at stage `n`; indexing by `n+1` avoids a special
zero stage while still tending to zero. -/
def stageError (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ)⁻¹

theorem stageError_pos (n : ℕ) : 0 < stageError n := by
  unfold stageError
  positivity

theorem tendsto_stageError : Tendsto stageError atTop (nhds 0) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  change Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0)
  simpa only [one_div, Nat.cast_add, Nat.cast_one] using h

private theorem innerPolynomial_norm_bounded (n : ℕ) (p : Polynomial) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun k ↦ ‖eval (fun j ↦ innerGeneratorLift B hB i a n j k) p‖) := by
  let s : BoundedMatrixSequence (fun k ↦ innerModel B hB n k) :=
    eval (innerGeneratorLift B hB i a n) p
  refine ⟨‖s‖, show ∀ᶠ k : ℕ in atTop,
      ‖eval (fun j ↦ innerGeneratorLift B hB i a n j k) p‖ ≤ ‖s‖ from
    Eventually.of_forall fun (k : ℕ) ↦ ?_⟩
  have h := boundedMatrixSequence_coord_norm_le
    (fun r ↦ innerModel B hB n r) s k
  have heval := congrArg norm
    (NormMatrixCoronaPolynomialLifts.eval_generatorLift_apply
      (fun r ↦ innerModel B hB n r) (innerEmbedding B hB n)
      (fun j ↦ reducedProductGeneratorLift B i a j n) p k)
  calc
    ‖eval (fun j ↦ innerGeneratorLift B hB i a n j k) p‖ =
        ‖eval (innerGeneratorLift B hB i a n) p k‖ := by
      change
        ‖eval (fun j ↦
            NormMatrixCoronaPolynomialLifts.generatorLift
              (fun r ↦ innerModel B hB n r) (innerEmbedding B hB n)
              (fun r ↦ reducedProductGeneratorLift B i a r n) j k) p‖ =
          ‖eval
            (NormMatrixCoronaPolynomialLifts.generatorLift
              (fun r ↦ innerModel B hB n r) (innerEmbedding B hB n)
              (fun r ↦ reducedProductGeneratorLift B i a r n)) p k‖
      exact heval.symm
    _ ≤ ‖s‖ := by simpa only [s] using h

/-- There is one threshold beyond which the upper norm estimate holds for all
of the first `n+1` polynomials. -/
theorem exists_commonUpperThreshold (n : ℕ) :
    ∃ K : ℕ, ∀ k, K ≤ k → ∀ r : Fin (n + 1),
      ‖eval (fun j ↦ innerGeneratorLift B hB i a n j k) (enumeration r)‖ <
        ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n)
          (enumeration r)‖ + stageError n := by
  have hall : ∀ᶠ k in atTop, ∀ r : Fin (n + 1),
      ‖eval (fun j ↦ innerGeneratorLift B hB i a n j k) (enumeration r)‖ <
        ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n)
          (enumeration r)‖ + stageError n := by
    apply Filter.eventually_all.mpr
    intro r
    have hlim := norm_innerPolynomial_eq_limsup B hB i a n (enumeration r)
    have hev : ∀ᶠ k in cofinite,
        ‖eval (fun j ↦ innerGeneratorLift B hB i a n j k) (enumeration r)‖ <
          ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n)
            (enumeration r)‖ + stageError n := by
      apply Filter.eventually_lt_of_limsup_lt
      · rw [← hlim]
        exact lt_add_of_pos_right _ (stageError_pos n)
      · simpa only [Nat.cofinite_eq_atTop] using
          innerPolynomial_norm_bounded B i a hB n (enumeration r)
    simpa only [Nat.cofinite_eq_atTop] using hev
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hall
  exact ⟨K, fun k hk ↦ hK k hk⟩

/-- A chosen common upper threshold. -/
def commonUpperThreshold (n : ℕ) : ℕ :=
  Classical.choose (exists_commonUpperThreshold B i a hB n)

theorem commonUpperThreshold_spec (n k : ℕ)
    (hk : commonUpperThreshold B i a hB n ≤ k) (r : Fin (n + 1)) :
    ‖eval (fun j ↦ innerGeneratorLift B hB i a n j k) (enumeration r)‖ <
      ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n)
        (enumeration r)‖ + stageError n :=
  Classical.choose_spec (exists_commonUpperThreshold B i a hB n) k hk r

end

end ReducedProductMFFiniteSelection
end GroupApproximation
