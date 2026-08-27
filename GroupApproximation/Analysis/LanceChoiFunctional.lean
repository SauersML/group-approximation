import GroupApproximation.Analysis.LanceMatrixSubalgebra
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The Choi functional of a completely positive map into matrices

Toward proof-ledger row `RE.05` (the Lance debt).  A map `Φ` from a star
subalgebra `C` into `B(ℂᵏ)` determines a scalar functional on the matrices
over `C` — the **Choi functional**

  `s(b) = ∑ p q, ⟪e_p, Φ (b p q) e_q⟫` —

whose positivity on ambient positives encodes the complete positivity of
`Φ`.  This file constructs the functional and proves:

* `choiForm_conj` — the completely positive form is real when `Φ` commutes
  with the star, by the conjugate-reindex argument;
* `choiFunctional_nonneg` — on a matrix that is positive in the ambient
  order the functional takes a nonnegative real value: factor
  `b = star N * N` with entries of `N` in `C`
  (`LanceMatrixSubalgebra.exists_entries_mem_factor`), split the value into
  one completely positive form per row of `N`, and use the form
  hypothesis at the standard basis vectors;
* `choiFunctional_single` — evaluation on a single-entry matrix recovers
  the matrix coefficients of `Φ`, which is how the extension will be read
  back into an operator-valued map.

This is exactly the hypothesis shape of
`StateExtension.exists_positive_extension`, the Krein extension already in
the tree.

## Manuscript status

Infrastructure for the Lance lane; certifies no manuscript step on its own.
`RE.05` remains conditional until the full compression statement lands.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace

noncomputable section

variable {A : Type} [CStarAlgebra A]
variable (C : StarSubalgebra ℂ A) {k : ℕ}
variable (Φ : ↥C →ₗ[ℂ]
  (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)))

/-- The entry of a matrix over the subalgebra, as an element of the
subalgebra. -/
def matrixEntry (b : ↥(matrixStarSubalgebra C k)) (p q : Fin k) : ↥C :=
  ⟨(b : CStarMatrix (Fin k) (Fin k) A) p q, b.2 p q⟩

/-- **The Choi functional** of `Φ`, on matrices over the subalgebra. -/
def choiFunctional : ↥(matrixStarSubalgebra C k) →ₗ[ℂ] ℂ where
  toFun b := ∑ p : Fin k, ∑ q : Fin k,
    ⟪EuclideanSpace.single p (1 : ℂ),
      Φ (matrixEntry C b p q) (EuclideanSpace.single q (1 : ℂ))⟫_ℂ
  map_add' b c := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    have h : matrixEntry C (b + c) p q
        = matrixEntry C b p q + matrixEntry C c p q := rfl
    rw [h, map_add, add_apply, inner_add_right]
  map_smul' z b := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    have h : matrixEntry C (z • b) p q = z • matrixEntry C b p q := rfl
    rw [h, map_smul, smul_apply, inner_smul_right, smul_eq_mul]

@[simp]
theorem choiFunctional_apply (b : ↥(matrixStarSubalgebra C k)) :
    choiFunctional C Φ b = ∑ p : Fin k, ∑ q : Fin k,
      ⟪EuclideanSpace.single p (1 : ℂ),
        Φ (matrixEntry C b p q) (EuclideanSpace.single q (1 : ℂ))⟫_ℂ := rfl

/-- The completely positive form is conjugation-invariant when `Φ` commutes
with the star. -/
theorem choiForm_conj (hstar : ∀ c : ↥C, Φ (star c) = star (Φ c))
    {m : ℕ} (a : Fin m → ↥C) (v : Fin m → EuclideanSpace ℂ (Fin k)) :
    (starRingEnd ℂ) (∑ i : Fin m, ∑ j : Fin m,
        ⟪v i, Φ (star (a i) * a j) (v j)⟫_ℂ)
      = ∑ i : Fin m, ∑ j : Fin m, ⟪v i, Φ (star (a i) * a j) (v j)⟫_ℂ := by
  rw [map_sum]
  have hterm : ∀ i j : Fin m,
      (starRingEnd ℂ) ⟪v i, Φ (star (a i) * a j) (v j)⟫_ℂ
        = ⟪v j, Φ (star (a j) * a i) (v i)⟫_ℂ := by
    intro i j
    rw [inner_conj_symm]
    have h1 : ⟪Φ (star (a i) * a j) (v j), v i⟫_ℂ
        = ⟪v j, ContinuousLinearMap.adjoint (Φ (star (a i) * a j))
            (v i)⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
    rw [h1, ← ContinuousLinearMap.star_eq_adjoint, ← hstar]
    have h2 : star (star (a i) * a j) = star (a j) * a i := by
      rw [star_mul, star_star]
    rw [h2]
  rw [Finset.sum_congr rfl fun i _ ↦ map_sum _ _ _]
  rw [Finset.sum_congr rfl fun i _ ↦
    Finset.sum_congr rfl fun j _ ↦ hterm i j]
  exact Finset.sum_comm

/-- A conjugation-invariant complex number is its real part. -/
theorem eq_re_of_conj_eq {z : ℂ} (h : (starRingEnd ℂ) z = z) :
    z = (z.re : ℂ) := by
  have him : z.im = 0 := by
    have h2 := congrArg Complex.im h
    rw [Complex.conj_im] at h2
    linarith
  refine Complex.ext ?_ ?_
  · rw [Complex.ofReal_re]
  · rw [Complex.ofReal_im, him]

/-- **The Choi functional is nonnegative on ambient positives.**  Factor the
matrix inside the closed subalgebra, split the value into one completely
positive form per row of the factor, and evaluate the form hypothesis at
standard basis vectors. -/
theorem choiFunctional_nonneg
    [PartialOrder A] [StarOrderedRing A]
    (hC : IsClosed (C : Set A))
    (hform : ∀ (m : ℕ) (a : Fin m → ↥C)
      (v : Fin m → EuclideanSpace ℂ (Fin k)),
      0 ≤ (∑ i : Fin m, ∑ j : Fin m,
        ⟪v i, Φ (star (a i) * a j) (v j)⟫_ℂ).re)
    (hstar : ∀ c : ↥C, Φ (star c) = star (Φ c))
    (b : ↥(matrixStarSubalgebra C k))
    (hb : 0 ≤ (b : CStarMatrix (Fin k) (Fin k) A)) :
    ∃ r : ℝ, 0 ≤ r ∧ choiFunctional C Φ b = r := by
  classical
  obtain ⟨N, hNmem, hNfact⟩ := exists_entries_mem_factor C hC b.2 hb
  -- the rows of the factor, inside the subalgebra
  set nn : Fin k → Fin k → ↥C := fun r s ↦ ⟨N r s, hNmem r s⟩ with hnn_def
  -- the entries of `b` split as sums over the rows
  have hentry : ∀ p q : Fin k, matrixEntry C b p q
      = ∑ r : Fin k, star (nn r p) * nn r q := by
    intro p q
    refine Subtype.ext ?_
    have hval : ((∑ r : Fin k, star (nn r p) * nn r q : ↥C) : A)
        = ∑ r : Fin k, star (N r p) * N r q := by
      rw [AddSubmonoidClass.coe_finsetSum]
      exact Finset.sum_congr rfl fun r _ ↦ rfl
    rw [hval]
    show (b : CStarMatrix (Fin k) (Fin k) A) p q
      = ∑ r : Fin k, star (N r p) * N r q
    rw [hNfact]
    exact Matrix.mul_apply
  -- the value splits as one form per row
  have hsplit : choiFunctional C Φ b
      = ∑ r : Fin k, ∑ p : Fin k, ∑ q : Fin k,
          ⟪EuclideanSpace.single p (1 : ℂ),
            Φ (star (nn r p) * nn r q)
              (EuclideanSpace.single q (1 : ℂ))⟫_ℂ := by
    rw [choiFunctional_apply]
    rw [Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by
      rw [hentry p q, map_sum, sum_apply, inner_sum]]
    calc ∑ p : Fin k, ∑ q : Fin k, ∑ r : Fin k,
          ⟪EuclideanSpace.single p (1 : ℂ),
            Φ (star (nn r p) * nn r q)
              (EuclideanSpace.single q (1 : ℂ))⟫_ℂ
        = ∑ p : Fin k, ∑ r : Fin k, ∑ q : Fin k,
            ⟪EuclideanSpace.single p (1 : ℂ),
              Φ (star (nn r p) * nn r q)
                (EuclideanSpace.single q (1 : ℂ))⟫_ℂ :=
          Finset.sum_congr rfl fun p _ ↦ Finset.sum_comm
      _ = ∑ r : Fin k, ∑ p : Fin k, ∑ q : Fin k,
            ⟪EuclideanSpace.single p (1 : ℂ),
              Φ (star (nn r p) * nn r q)
                (EuclideanSpace.single q (1 : ℂ))⟫_ℂ :=
          Finset.sum_comm
  -- each row form is a real nonnegative number
  have hrow : ∀ r : Fin k, ∃ t : ℝ, 0 ≤ t ∧
      (∑ p : Fin k, ∑ q : Fin k,
        ⟪EuclideanSpace.single p (1 : ℂ),
          Φ (star (nn r p) * nn r q)
            (EuclideanSpace.single q (1 : ℂ))⟫_ℂ) = t := by
    intro r
    set F := ∑ p : Fin k, ∑ q : Fin k,
      ⟪EuclideanSpace.single p (1 : ℂ),
        Φ (star (nn r p) * nn r q)
          (EuclideanSpace.single q (1 : ℂ))⟫_ℂ with hF_def
    have hre : 0 ≤ F.re :=
      hform k (fun s ↦ nn r s) (fun s ↦ EuclideanSpace.single s (1 : ℂ))
    have hconj : (starRingEnd ℂ) F = F :=
      choiForm_conj C Φ hstar (fun s ↦ nn r s)
        (fun s ↦ EuclideanSpace.single s (1 : ℂ))
    exact ⟨F.re, hre, eq_re_of_conj_eq hconj⟩
  choose t ht1 ht2 using hrow
  refine ⟨∑ r : Fin k, t r, Finset.sum_nonneg fun r _ ↦ ht1 r, ?_⟩
  rw [hsplit, Finset.sum_congr rfl fun r _ ↦ ht2 r]
  rw [Complex.ofReal_sum]

/-- Single-entry matrices lie in the entrywise subalgebra. -/
theorem single_mem_matrixStarSubalgebra (c : ↥C) (p₀ q₀ : Fin k) :
    (Matrix.single p₀ q₀ (c : A) : CStarMatrix (Fin k) (Fin k) A)
      ∈ matrixStarSubalgebra C k := by
  intro p q
  classical
  rw [Matrix.single_apply]
  split
  · exact c.2
  · exact zero_mem C

/-- Evaluation of the Choi functional on a single-entry matrix recovers
the matrix coefficient of `Φ`. -/
theorem choiFunctional_single (c : ↥C) (p₀ q₀ : Fin k) :
    choiFunctional C Φ
        ⟨(Matrix.single p₀ q₀ (c : A) : CStarMatrix (Fin k) (Fin k) A),
          single_mem_matrixStarSubalgebra C c p₀ q₀⟩
      = ⟪EuclideanSpace.single p₀ (1 : ℂ),
          Φ c (EuclideanSpace.single q₀ (1 : ℂ))⟫_ℂ := by
  classical
  rw [choiFunctional_apply]
  have hzero : ∀ p q : Fin k, ¬(p₀ = p ∧ q₀ = q) →
      matrixEntry C
        ⟨(Matrix.single p₀ q₀ (c : A) : CStarMatrix (Fin k) (Fin k) A),
          single_mem_matrixStarSubalgebra C c p₀ q₀⟩ p q = 0 := by
    intro p q hne
    refine Subtype.ext ?_
    show (Matrix.single p₀ q₀ (c : A)) p q = 0
    rw [Matrix.single_apply, if_neg hne]
  have hsame : matrixEntry C
      ⟨(Matrix.single p₀ q₀ (c : A) : CStarMatrix (Fin k) (Fin k) A),
        single_mem_matrixStarSubalgebra C c p₀ q₀⟩ p₀ q₀ = c := by
    refine Subtype.ext ?_
    show (Matrix.single p₀ q₀ (c : A)) p₀ q₀ = (c : A)
    rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩]
  rw [Finset.sum_eq_single p₀ (fun p _ hp ↦ ?_)
    (fun h ↦ absurd (Finset.mem_univ p₀) h)]
  · rw [Finset.sum_eq_single q₀ (fun q _ hq ↦ ?_)
      (fun h ↦ absurd (Finset.mem_univ q₀) h)]
    · rw [hsame]
    · rw [hzero p₀ q (fun hpq ↦ hq hpq.2.symm), map_zero,
        zero_apply, inner_zero_right]
  · refine Finset.sum_eq_zero fun q _ ↦ ?_
    rw [hzero p q (fun hpq ↦ hp hpq.1.symm), map_zero,
      zero_apply, inner_zero_right]

end

end CStarExactness
end GroupApproximation
