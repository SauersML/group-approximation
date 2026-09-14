import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import GroupApproximation.Meta.AxiomGuard

/-!
# Star homomorphisms out of matrix algebras from systems of matrix units

Infrastructure of lane `oa-hyperfinite` for "Brown's formulation" of `simple_kazhdan_sofic_group.tex`
(tex l.273–290 at 37551fd93).  The unital trace-preserving embeddings `M_{2^j} → 𝓡` of the Pauli
stages and the corner embeddings `M_k → M_{2^j}` behind `∏_ω M_k → 𝓡^ω` are both built from a
system of matrix units by the construction of this module.

For a complex star algebra `A` and a family `E : n → n → A` with `E a b * E c d = [b = c] E a d` and
`(E a b)⋆ = E b a`:

* `matrixUnitSum E A := Σ_{a,b} A a b • E a b`.
* `matrixUnitSum_mul`, `matrixUnitSum_star`, `matrixUnitSum_add`, `matrixUnitSum_smul`: it is
  multiplicative, star-preserving and linear.
* `matrixUnitHom`: when `Σ_a E a a = 1` it is a unital star algebra homomorphism
  `Matrix n n ℂ →⋆ₐ[ℂ] A`.
* `trace_matrixUnitSum`: a linear functional with `τ (E a b) = [a = b] c` sends `matrixUnitSum E A`
  to `c · trace A`.
-/

namespace GroupApproximation
namespace MatrixUnits

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- A **system of matrix units** indexed by `n` in `A`. -/
structure IsMatrixUnits (E : n → n → A) : Prop where
  mul : ∀ a b c d, E a b * E c d = if b = c then E a d else 0
  star : ∀ a b, star (E a b) = E b a

/-- `Σ_{a,b} A a b • E a b`. -/
def matrixUnitSum (E : n → n → A) (M : Matrix n n ℂ) : A :=
  ∑ a, ∑ b, M a b • E a b

theorem matrixUnitSum_add (E : n → n → A) (M N : Matrix n n ℂ) :
    matrixUnitSum E (M + N) = matrixUnitSum E M + matrixUnitSum E N := by
  simp only [matrixUnitSum, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem matrixUnitSum_smul (E : n → n → A) (c : ℂ) (M : Matrix n n ℂ) :
    matrixUnitSum E (c • M) = c • matrixUnitSum E M := by
  simp only [matrixUnitSum, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem matrixUnitSum_zero (E : n → n → A) : matrixUnitSum E (0 : Matrix n n ℂ) = 0 := by
  simp [matrixUnitSum]

theorem matrixUnitSum_mul {E : n → n → A} (hE : IsMatrixUnits E) (M N : Matrix n n ℂ) :
    matrixUnitSum E (M * N) = matrixUnitSum E M * matrixUnitSum E N := by
  have hprod : matrixUnitSum E M * matrixUnitSum E N =
      ∑ a, ∑ b, ∑ c, ∑ d, (M a b * N c d) • (E a b * E c d) := by
    simp only [matrixUnitSum, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
  rw [hprod]
  simp only [hE.mul, smul_ite, smul_zero]
  have hinner : ∀ a b, (∑ c, ∑ d, if b = c then (M a b * N c d) • E a d else 0) =
      ∑ d, (M a b * N b d) • E a d := by
    intro a b
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [Finset.sum_ite_eq]
    simp
  simp only [hinner]
  rw [matrixUnitSum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [Matrix.mul_apply, Finset.sum_smul]

theorem matrixUnitSum_star {E : n → n → A} (hE : IsMatrixUnits E) (M : Matrix n n ℂ) :
    matrixUnitSum E (star M) = star (matrixUnitSum E M) := by
  simp only [matrixUnitSum, star_sum, star_smul, hE.star, Matrix.star_apply]
  rw [Finset.sum_comm]

theorem matrixUnitSum_one {E : n → n → A} (hsum : ∑ a, E a a = 1) :
    matrixUnitSum E (1 : Matrix n n ℂ) = 1 := by
  simp only [matrixUnitSum, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  rw [← hsum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_ite_eq]
  simp

/-- **The star algebra homomorphism of a unital system of matrix units.** -/
def matrixUnitHom {E : n → n → A} (hE : IsMatrixUnits E) (hsum : ∑ a, E a a = 1) :
    Matrix n n ℂ →⋆ₐ[ℂ] A where
  toFun := matrixUnitSum E
  map_one' := matrixUnitSum_one hsum
  map_mul' := matrixUnitSum_mul hE
  map_zero' := matrixUnitSum_zero E
  map_add' := matrixUnitSum_add E
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, matrixUnitSum_smul,
      matrixUnitSum_one hsum]
  map_star' := matrixUnitSum_star hE

theorem matrixUnitHom_apply {E : n → n → A} (hE : IsMatrixUnits E) (hsum : ∑ a, E a a = 1)
    (M : Matrix n n ℂ) : matrixUnitHom hE hsum M = ∑ a, ∑ b, M a b • E a b :=
  rfl

/-- **Trace transfer.**  A linear functional taking the value `[a = b] c` on the matrix units takes
`c · trace M` on `matrixUnitSum E M`. -/
theorem trace_matrixUnitSum (E : n → n → A) (τ : A →ₗ[ℂ] ℂ) (c : ℂ)
    (hτ : ∀ a b, τ (E a b) = if a = b then c else 0) (M : Matrix n n ℂ) :
    τ (matrixUnitSum E M) = c * Matrix.trace M := by
  simp only [matrixUnitSum, map_sum, map_smul, hτ, smul_eq_mul, mul_ite, mul_zero]
  rw [Matrix.trace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_ite_eq]
  simp [mul_comm]

end

#audit_axioms matrixUnitSum_mul
#audit_axioms trace_matrixUnitSum

end MatrixUnits
end GroupApproximation
