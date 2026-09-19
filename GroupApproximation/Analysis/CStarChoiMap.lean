import GroupApproximation.Analysis.CStarCompletelyPositiveForm
import GroupApproximation.Analysis.CStarMatrixFactorization

/-!
# Choi-type maps out of a matrix algebra are completely positive

Every completely positive map *out of* `B(ℂᵏ)` has the form

  `Θ_b(T) = ∑_{p,q} T_{pq} · b_p⋆ b_q`

for a `k`-tuple `b` in the target, and conversely every such map is
completely positive.  This file proves the converse direction, which is the
one a construction needs: it is what makes the Følner map of the Lance lane
--- `T ↦ ∑ T_{pq} ξ_p ξ_q λ_p λ_q⋆` --- completely positive, with no
tensor-product vocabulary and no amplification bound.

The proof is the Choi computation carried out on matrices.  A positive `Y`
over `B(ℂᵏ)` factors as `Z⋆Z`; expanding the entries of `Z` in the standard
basis of `ℂᵏ` turns `Y.map Θ_b` into a sum, over the pairs `(r, u)` of a row
index and a basis index, of rank-one matrices `(i, j) ↦ w_i⋆ w_j` --- and
those are positive by the column trick `star_col_mul_col`.

* `euclideanEntryLM` --- the `(p,q)` matrix entry of an operator on `ℂᵏ`, as
  a linear functional, so that `map_sum` applies to it;
* `euclideanEntry_star`, `euclideanEntry_mul` --- the two ⋆-homomorphism
  clauses the computation uses;
* `choiMap`, `isCompletelyPositive_choiMap` --- **the theorem**.

`star_col_mul_col` needs a row index, so the rank-one step assumes
`NeZero n` and the empty matrix level is discharged separately.

## Manuscript status

Infrastructure for the Lance lane; certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace
open Finset

universe u

/-! ## A four-fold sum reordering -/

/-- Swapping an outer pair of summations past an inner pair, by viewing each
pair as a single sum over a product type. -/
theorem sum_swap_pairs {ι κ ρ σ M : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    [Fintype σ] [AddCommMonoid M] (F : ι → κ → ρ → σ → M) :
    (∑ p : ι, ∑ q : κ, ∑ r : ρ, ∑ u : σ, F p q r u)
      = ∑ r : ρ, ∑ u : σ, ∑ p : ι, ∑ q : κ, F p q r u := by
  calc (∑ p : ι, ∑ q : κ, ∑ r : ρ, ∑ u : σ, F p q r u)
      = ∑ p : ι, ∑ r : ρ, ∑ q : κ, ∑ u : σ, F p q r u :=
        Finset.sum_congr rfl fun p _ ↦ Finset.sum_comm
    _ = ∑ r : ρ, ∑ p : ι, ∑ q : κ, ∑ u : σ, F p q r u := Finset.sum_comm
    _ = ∑ r : ρ, ∑ u : σ, ∑ p : ι, ∑ q : κ, F p q r u := by
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        calc (∑ p : ι, ∑ q : κ, ∑ u : σ, F p q r u)
            = ∑ p : ι, ∑ u : σ, ∑ q : κ, F p q r u :=
              Finset.sum_congr rfl fun p _ ↦ Finset.sum_comm
          _ = ∑ u : σ, ∑ p : ι, ∑ q : κ, F p q r u := Finset.sum_comm

variable {B : Type u} [NonUnitalCStarAlgebra B]

noncomputable section

/-! ## Matrix entries of an operator on `ℂᵏ` -/

/-- The `(p, q)` entry of an operator on `ℂᵏ`, as a linear functional of the
operator. -/
def euclideanEntryLM (k : ℕ) (p q : Fin k) :
    (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) →ₗ[ℂ] ℂ where
  toFun T := ⟪(EuclideanSpace.single p (1 : ℂ) : EuclideanSpace ℂ (Fin k)),
    T (EuclideanSpace.single q (1 : ℂ))⟫_ℂ
  map_add' S T := by
    simp
  map_smul' r T := by
    simp

theorem euclideanEntryLM_apply {k : ℕ} (p q : Fin k)
    (T : EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) :
    euclideanEntryLM k p q T
      = ⟪(EuclideanSpace.single p (1 : ℂ) : EuclideanSpace ℂ (Fin k)),
          T (EuclideanSpace.single q (1 : ℂ))⟫_ℂ :=
  rfl

/-- Expansion of an inner product on `ℂᵏ` over the standard basis. -/
theorem euclidean_inner_expand {k : ℕ} (a c : EuclideanSpace ℂ (Fin k)) :
    ⟪a, c⟫_ℂ = ∑ u : Fin k,
      star ⟪(EuclideanSpace.single u (1 : ℂ) : EuclideanSpace ℂ (Fin k)), a⟫_ℂ
        * ⟪(EuclideanSpace.single u (1 : ℂ) : EuclideanSpace ℂ (Fin k)), c⟫_ℂ := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left,
    map_one, one_mul, one_mul, RCLike.inner_apply', starRingEnd_apply]

/-- The entries of an adjoint are the conjugate transposed entries. -/
theorem euclideanEntry_star {k : ℕ} (p q : Fin k)
    (S : EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) :
    euclideanEntryLM k p q (star S) = star (euclideanEntryLM k q p S) := by
  rw [euclideanEntryLM_apply, euclideanEntryLM_apply,
    ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm,
    starRingEnd_apply]

/-- The entries of a product are the matrix product of the entries. -/
theorem euclideanEntry_mul {k : ℕ} (p q : Fin k)
    (S T : EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) :
    euclideanEntryLM k p q (S * T)
      = ∑ u : Fin k, euclideanEntryLM k p u S * euclideanEntryLM k u q T := by
  have hmul : (S * T) (EuclideanSpace.single q (1 : ℂ))
      = S (T (EuclideanSpace.single q (1 : ℂ))) := rfl
  rw [euclideanEntryLM_apply, hmul, ← ContinuousLinearMap.adjoint_inner_left,
    euclidean_inner_expand
      (ContinuousLinearMap.adjoint S (EuclideanSpace.single p (1 : ℂ)))
      (T (EuclideanSpace.single q (1 : ℂ)))]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  have hstar : ⟪(EuclideanSpace.single u (1 : ℂ) : EuclideanSpace ℂ (Fin k)),
      ContinuousLinearMap.adjoint S (EuclideanSpace.single p (1 : ℂ))⟫_ℂ
      = star (euclideanEntryLM k p u S) := by
    rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm,
      euclideanEntryLM_apply, starRingEnd_apply]
  rw [hstar, star_star, euclideanEntryLM_apply, euclideanEntryLM_apply]

/-! ## The Choi-type map -/

/-- **The Choi-type map** `Θ_b(T) = ∑_{p,q} T_{pq} · b_p⋆ b_q`. -/
def choiMap {k : ℕ} (b : Fin k → B) :
    (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) →ₗ[ℂ] B where
  toFun T := ∑ p : Fin k, ∑ q : Fin k,
    euclideanEntryLM k p q T • (star (b p) * b q)
  map_add' S T := by
    simp [map_add, add_smul, Finset.sum_add_distrib]
  map_smul' r T := by
    simp [map_smul, smul_smul, Finset.smul_sum]

theorem choiMap_apply {k : ℕ} (b : Fin k → B)
    (T : EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) :
    choiMap b T
      = ∑ p : Fin k, ∑ q : Fin k,
          euclideanEntryLM k p q T • (star (b p) * b q) :=
  rfl

/-! ## Complete positivity -/

variable [PartialOrder B] [StarOrderedRing B]

/-- The rank-one matrix `(i, j) ↦ w_i⋆ w_j` is positive. -/
theorem rankOne_nonneg {n : ℕ} [NeZero n] (w : Fin n → B) :
    (0 : CStarMatrix (Fin n) (Fin n) B)
      ≤ CStarMatrix.ofMatrix (Matrix.of fun i j ↦ star (w i) * w j) := by
  obtain ⟨N, hN⟩ := star_col_mul_col w
  rw [hN]
  exact star_mul_self_nonneg N

omit [PartialOrder B] [StarOrderedRing B] in
/-- The rank-one expansion of `star w_i * w_j` when each `w` is a linear
combination of the tuple `b`. -/
theorem star_combination_mul_combination {k : ℕ} (b : Fin k → B)
    (c d : Fin k → ℂ) :
    star (∑ p : Fin k, c p • b p) * (∑ q : Fin k, d q • b q)
      = ∑ p : Fin k, ∑ q : Fin k,
          (star (c p) * d q) • (star (b p) * b q) := by
  rw [star_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [star_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

/-- **Choi-type maps are completely positive.** -/
theorem isCompletelyPositive_choiMap {k : ℕ} (b : Fin k → B) :
    IsCompletelyPositive (choiMap b) := by
  classical
  -- The order on `B(ℂᵏ)` is deliberately not an instance in Mathlib --- an
  -- algebra may carry a partial order with better definitional properties ---
  -- so the spectral one is invoked here.  It is used only to reach the
  -- positivity criterion; the statement mentions no order.
  letI : PartialOrder (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) :=
    CStarAlgebra.spectralOrder _
  letI : StarOrderedRing (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) :=
    CStarAlgebra.spectralOrderedRing _
  refine isCompletelyPositive_of_map_nonneg _ fun n Y hY ↦ ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine le_of_eq ?_
    funext i
    exact i.elim0
  · haveI : NeZero n := ⟨by omega⟩
    obtain ⟨Z, hZ⟩ := exists_star_mul_self_of_nonneg hY
    set w : Fin n → Fin k → Fin n → B := fun r u i ↦
      ∑ p : Fin k, euclideanEntryLM k u p (Z r i) • b p with hw
    have hentry : ∀ i j : Fin n, (Y.map ⇑(choiMap b)) i j
        = ∑ r : Fin n, ∑ u : Fin k, star (w r u i) * w r u j := by
      intro i j
      have hYij : Y i j = ∑ r : Fin n, star (Z r i) * Z r j := by
        rw [hZ, cstarMatrix_mul_apply]
        exact Finset.sum_congr rfl fun r _ ↦ by rw [cstarMatrix_star_apply]
      have hmapentry : (Y.map ⇑(choiMap b)) i j = choiMap b (Y i j) := rfl
      have hcoef : ∀ p q : Fin k,
          euclideanEntryLM k p q (Y i j)
            = ∑ r : Fin n, ∑ u : Fin k,
                star (euclideanEntryLM k u p (Z r i))
                  * euclideanEntryLM k u q (Z r j) := by
        intro p q
        rw [hYij, map_sum]
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        rw [euclideanEntry_mul]
        exact Finset.sum_congr rfl fun u _ ↦ by rw [euclideanEntry_star]
      have hleft : (Y.map ⇑(choiMap b)) i j
          = ∑ p : Fin k, ∑ q : Fin k, ∑ r : Fin n, ∑ u : Fin k,
              (star (euclideanEntryLM k u p (Z r i))
                * euclideanEntryLM k u q (Z r j)) • (star (b p) * b q) := by
        rw [hmapentry, choiMap_apply]
        refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
        rw [hcoef p q, Finset.sum_smul]
        exact Finset.sum_congr rfl fun r _ ↦ Finset.sum_smul
      have hright : ∀ r : Fin n, ∀ u : Fin k,
          star (w r u i) * w r u j
            = ∑ p : Fin k, ∑ q : Fin k,
                (star (euclideanEntryLM k u p (Z r i))
                  * euclideanEntryLM k u q (Z r j)) • (star (b p) * b q) := by
        intro r u
        rw [hw]
        exact star_combination_mul_combination b _ _
      rw [hleft, sum_swap_pairs
        (fun p q r u ↦ (star (euclideanEntryLM k u p (Z r i))
          * euclideanEntryLM k u q (Z r j)) • (star (b p) * b q))]
      exact (Finset.sum_congr rfl fun r _ ↦
        Finset.sum_congr rfl fun u _ ↦ hright r u).symm
    have hsum : Y.map ⇑(choiMap b)
        = ∑ r : Fin n, ∑ u : Fin k,
            CStarMatrix.ofMatrix
              (Matrix.of fun i j ↦ star (w r u i) * w r u j) := by
      -- `CStarMatrix` is a type synonym for `Matrix`, and a sum of them
      -- cannot be applied to an index until the synonym is unfolded; the
      -- ascription does that, after which the entry argument is the ordinary
      -- one about a sum of functions.
      show (Y.map ⇑(choiMap b) : Matrix (Fin n) (Fin n) B)
          = ∑ r : Fin n, ∑ u : Fin k,
              ((Matrix.of fun i j ↦ star (w r u i) * w r u j) :
                Matrix (Fin n) (Fin n) B)
      funext i j
      rw [hentry i j]
      simp only [Matrix.sum_apply, Matrix.of_apply]
    rw [hsum]
    exact Finset.sum_nonneg fun r _ ↦
      Finset.sum_nonneg fun u _ ↦ rankOne_nonneg (w r u)

end

end CStarExactness
end GroupApproximation
