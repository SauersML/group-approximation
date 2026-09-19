import GroupApproximation.GGT.HullSCUnionGeometryBranchPoint

/-!
# The factor's acylindricity, as a statement about one long letter

Acylindricity of a factor is a statement about two points of its Cayley graph.
The free-product estimate needs it at one particular pair --- the two ends of a
long letter `τ`, that is the basepoint and its translate by `τ` --- and in the
vocabulary of word length rather than of `dist`.  This module performs that
translation once.

`exists_factorDisplacement_bound`: from `IsAcylindrical F (Cayley A)` and `ε > 0`
there are `R` and `N` with

    R ≤ |τ|  ⟹  #{γ : |γ| ≤ ε and |τ⁻¹ γ τ| ≤ ε} ≤ N .

The proof is the definition read at `x := 1` and `y := τ`: `dist 1 τ = |τ|`,
`dist 1 (γ · 1) = |γ|` and `dist τ (γ · τ) = |τ⁻¹ γ τ|`, all three by
`wordDist S x y = wordNorm S (x⁻¹ * y)` and the definition of the translation
action.  This is the converse of the reduction
`isAcylindrical_cayley_of_conjDisplacement` performs, at a single pair of points
instead of all of them.
-/

namespace GroupApproximation
namespace HullSCUnionGeometry

open Monoid Monoid.CoprodI
open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry
open GroupApproximation.FreeProductCyclic
open GroupApproximation.FreeProductUnionNorm
open GroupApproximation.Manuscript.NonMF.TorsionFree

section FactorInput

/-- **The two-point displacement set of a factor, at the two ends of one
letter.** -/
theorem exists_factorDisplacement_bound {F : Type} [Group F] (A : Alphabet F)
    (hacyl : IsAcylindrical F (Cayley A)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : ℝ) (N : ℕ), ∀ τ : F, R ≤ ((wordNorm A.carrier τ : ℕ) : ℝ) →
      {γ : F | ((wordNorm A.carrier γ : ℕ) : ℝ) ≤ ε ∧
          ((wordNorm A.carrier (τ⁻¹ * γ * τ) : ℕ) : ℝ) ≤ ε}.Finite ∧
        {γ : F | ((wordNorm A.carrier γ : ℕ) : ℝ) ≤ ε ∧
          ((wordNorm A.carrier (τ⁻¹ * γ * τ) : ℕ) : ℝ) ≤ ε}.ncard ≤ N := by
  obtain ⟨R, N, hRN⟩ := hacyl ε hε
  refine ⟨R, N, ?_⟩
  intro τ hτ
  have hxy : dist (Cayley.of A 1) (Cayley.of A τ)
      = ((wordNorm A.carrier τ : ℕ) : ℝ) := by
    show ((wordNorm A.carrier ((1 : F)⁻¹ * τ) : ℕ) : ℝ)
      = ((wordNorm A.carrier τ : ℕ) : ℝ)
    rw [inv_one, one_mul]
  obtain ⟨hfin, hcard⟩ :=
    hRN (Cayley.of A 1) (Cayley.of A τ) (by rw [hxy]; exact hτ)
  have hseteq : {g : F | dist (Cayley.of A 1) (g • Cayley.of A 1) ≤ ε ∧
        dist (Cayley.of A τ) (g • Cayley.of A τ) ≤ ε}
      = {γ : F | ((wordNorm A.carrier γ : ℕ) : ℝ) ≤ ε ∧
          ((wordNorm A.carrier (τ⁻¹ * γ * τ) : ℕ) : ℝ) ≤ ε} := by
    ext γ
    have h1 : dist (Cayley.of A 1) (γ • Cayley.of A 1)
        = ((wordNorm A.carrier γ : ℕ) : ℝ) := by
      show ((wordNorm A.carrier ((1 : F)⁻¹ * (γ * 1)) : ℕ) : ℝ)
        = ((wordNorm A.carrier γ : ℕ) : ℝ)
      rw [inv_one, one_mul, mul_one]
    have h2 : dist (Cayley.of A τ) (γ • Cayley.of A τ)
        = ((wordNorm A.carrier (τ⁻¹ * γ * τ) : ℕ) : ℝ) := by
      show ((wordNorm A.carrier (τ⁻¹ * (γ * τ)) : ℕ) : ℝ)
        = ((wordNorm A.carrier (τ⁻¹ * γ * τ) : ℕ) : ℝ)
      rw [mul_assoc]
    simp only [Set.mem_setOf_eq, h1, h2]
  rw [hseteq] at hfin hcard
  exact ⟨hfin, hcard⟩

end FactorInput

end HullSCUnionGeometry
end GroupApproximation
