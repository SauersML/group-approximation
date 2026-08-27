import GroupApproximation.Analysis.ReducedProductMFFiniteSelection

/-!
# Designated coordinates in the reduced-product MF diagonal argument

This is the lower-selection half of finite simultaneous limsup selection.
It is separated from threshold construction so both compiler targets remain
small while retaining the original namespace and declaration names.
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

noncomputable local instance matrixBlockCStarAlgebraForDesignatedCoordinate
    (Z : Type*) [Fintype Z] [DecidableEq Z] [Nonempty Z] :
    CStarAlgebra (Matrix Z Z ℂ) where
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

/-- Beyond the common threshold, each designated polynomial has a coordinate
where its lower estimate is attained. -/
theorem exists_designatedCoordinate (n : ℕ) (r : Fin (n + 1)) :
    ∃ k : ℕ, commonUpperThreshold B i a hB n ≤ k ∧
      ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n)
          (enumeration r)‖ - stageError n <
        ‖eval (fun j ↦ innerGeneratorLift B hB i a n j k) (enumeration r)‖ := by
  have hlim := norm_innerPolynomial_eq_limsup B hB i a n (enumeration r)
  have hcob : IsCoboundedUnder (· ≤ ·) cofinite
      (fun k ↦ ‖eval (fun j ↦ innerGeneratorLift B hB i a n j k)
        (enumeration r)‖) :=
    Filter.isCoboundedUnder_le_of_le cofinite fun k ↦ norm_nonneg _
  have hfreq : ∃ᶠ k in cofinite,
      ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n)
          (enumeration r)‖ - stageError n <
        ‖eval (fun j ↦ innerGeneratorLift B hB i a n j k) (enumeration r)‖ := by
    apply Filter.frequently_lt_of_lt_limsup hcob
    rw [← hlim]
    linarith [stageError_pos n]
  have htail : ∀ᶠ k in cofinite, commonUpperThreshold B i a hB n ≤ k := by
    simpa only [Nat.cofinite_eq_atTop] using
      Filter.eventually_ge_atTop (commonUpperThreshold B i a hB n)
  obtain ⟨k, hlower, hk⟩ := (hfreq.and_eventually htail).exists
  exact ⟨k, hk, hlower⟩

/-- The selected inner coordinate `k_p` for a polynomial in the finite stage. -/
def designatedCoordinate (n : ℕ) (r : Fin (n + 1)) : ℕ :=
  Classical.choose (exists_designatedCoordinate B i a hB n r)

theorem designatedCoordinate_ge (n : ℕ) (r : Fin (n + 1)) :
    commonUpperThreshold B i a hB n ≤ designatedCoordinate B i a hB n r :=
  (Classical.choose_spec (exists_designatedCoordinate B i a hB n r)).1

theorem designatedCoordinate_lower (n : ℕ) (r : Fin (n + 1)) :
    ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n)
        (enumeration r)‖ - stageError n <
      ‖eval (fun j ↦ innerGeneratorLift B hB i a n j
        (designatedCoordinate B i a hB n r)) (enumeration r)‖ :=
  (Classical.choose_spec (exists_designatedCoordinate B i a hB n r)).2

/-- Every selected block satisfies every finite-stage upper bound because all
selected coordinates lie beyond the common threshold. -/
theorem designatedCoordinate_upper (n : ℕ) (r s : Fin (n + 1)) :
    ‖eval (fun j ↦ innerGeneratorLift B hB i a n j
        (designatedCoordinate B i a hB n s)) (enumeration r)‖ <
      ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n)
        (enumeration r)‖ + stageError n :=
  commonUpperThreshold_spec B i a hB n _
    (designatedCoordinate_ge B i a hB n s) r

end

end ReducedProductMFFiniteSelection
end GroupApproximation
