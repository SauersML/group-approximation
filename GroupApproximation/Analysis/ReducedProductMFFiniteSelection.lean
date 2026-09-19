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

noncomputable section

universe u v

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
  simp [stageError]

private theorem innerPolynomial_norm_bounded (n : ℕ) (p : Polynomial) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun k ↦ ‖eval (fun j ↦ innerGeneratorLift B i a hB n j k) p‖) := by
  let s : BoundedMatrixSequence (fun k ↦ innerModel B hB n k) :=
    eval (innerGeneratorLift B i a hB n) p
  refine ⟨‖s‖, Eventually.of_forall fun k ↦ ?_⟩
  have h := boundedMatrixSequence_coord_norm_le
    (fun r ↦ innerModel B hB n r) s k
  simpa [s, NormMatrixCoronaPolynomialLifts.eval_generatorLift_apply] using h

/-- There is one threshold beyond which the upper norm estimate holds for all
of the first `n+1` polynomials. -/
theorem exists_commonUpperThreshold (n : ℕ) :
    ∃ K : ℕ, ∀ k, K ≤ k → ∀ r : Fin (n + 1),
      ‖eval (fun j ↦ innerGeneratorLift B i a hB n j k) (enumeration r)‖ <
        ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n)
          (enumeration r)‖ + stageError n := by
  have hall : ∀ᶠ k in atTop, ∀ r : Fin (n + 1),
      ‖eval (fun j ↦ innerGeneratorLift B i a hB n j k) (enumeration r)‖ <
        ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n)
          (enumeration r)‖ + stageError n := by
    apply Filter.eventually_all.mpr
    intro r
    have hlim := norm_innerPolynomial_eq_limsup B i a hB n (enumeration r)
    have hev : ∀ᶠ k in cofinite,
        ‖eval (fun j ↦ innerGeneratorLift B i a hB n j k) (enumeration r)‖ <
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
    ‖eval (fun j ↦ innerGeneratorLift B i a hB n j k) (enumeration r)‖ <
      ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n)
        (enumeration r)‖ + stageError n :=
  Classical.choose_spec (exists_commonUpperThreshold B i a hB n) k hk r

/-- Beyond the common threshold, each designated polynomial has a coordinate
where its lower estimate is attained. -/
theorem exists_designatedCoordinate (n : ℕ) (r : Fin (n + 1)) :
    ∃ k : ℕ, commonUpperThreshold B i a hB n ≤ k ∧
      ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n)
          (enumeration r)‖ - stageError n <
        ‖eval (fun j ↦ innerGeneratorLift B i a hB n j k) (enumeration r)‖ := by
  have hlim := norm_innerPolynomial_eq_limsup B i a hB n (enumeration r)
  have hcob : IsCoboundedUnder (· ≤ ·) cofinite
      (fun k ↦ ‖eval (fun j ↦ innerGeneratorLift B i a hB n j k)
        (enumeration r)‖) :=
    Filter.isCoboundedUnder_le_of_le cofinite fun k ↦ norm_nonneg _
  have hfreq : ∃ᶠ k in cofinite,
      ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n)
          (enumeration r)‖ - stageError n <
        ‖eval (fun j ↦ innerGeneratorLift B i a hB n j k) (enumeration r)‖ := by
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
      ‖eval (fun j ↦ innerGeneratorLift B i a hB n j
        (designatedCoordinate B i a hB n r)) (enumeration r)‖ :=
  (Classical.choose_spec (exists_designatedCoordinate B i a hB n r)).2

/-- Every selected block satisfies every finite-stage upper bound because all
selected coordinates lie beyond the common threshold. -/
theorem designatedCoordinate_upper (n : ℕ) (r s : Fin (n + 1)) :
    ‖eval (fun j ↦ innerGeneratorLift B i a hB n j
        (designatedCoordinate B i a hB n s)) (enumeration r)‖ <
      ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n)
        (enumeration r)‖ + stageError n :=
  commonUpperThreshold_spec B i a hB n _
    (designatedCoordinate_ge B i a hB n s) r

end

end ReducedProductMFFiniteSelection
end GroupApproximation
