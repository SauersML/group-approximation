import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.Statement
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-25, part 1: the `cpap` field, the smaller Statement and one estimate

## Truth check of `NuclearDensityGapStatement.cpap`

The field is **true**.  A unital nuclear `A` has ucp maps `α : A → D` and `β : D → A`
through a finite-dimensional `D` with `βα ≈ id` on `F` (Choi--Effros perturbation of the
cpc factorization in `CStarExactness.IsNuclearMap`).  Embed `D ⊆ M_Y` unitally, and put
`ρ = ι ∘ α` and `ψ = β ∘ E`.  Choi's Cauchy--Schwarz inequality then gives the left
bimodule clause.  Separability is never used.  For trivial `A`, take `Y` empty.  The
topology is the norm topology throughout, pointwise on the finite set `F`.

The field does **not** close here: the corpus has no Choi--Effros lifting for cpc maps
into finite-dimensional algebras, and no structure theorem `D ≅ ⊕ M_{kᵢ}`.

## The smaller Statement `IsMatrixLeftBimoduleCPAP`

It is `IsMatrixCPAP` with three clauses deleted: the right bimodule clause and both
multiplicativity clauses.  So it is **strictly weaker as a clause list**, and it is
true for every nuclear `A` for the reason above.  The file `CloseCPAPReduction` proves
the three deleted clauses (`isMatrixCPAP_of_leftBimodule`):

* the right clause is the adjoint of the left clause at `star a`, because `ρ` and `ψ`
  preserve stars;
* both multiplicativity clauses follow from the left clause and `ψρ ≈ id`, applied on a
  larger finite set `G ⊇ F ∪ F⋆ ∪ F·F ∪ (F·F)⋆` with a tolerance scaled by `‖G‖³`.

This file holds the Statement, the one-step estimate `norm_bimod_step` and the first
multiplicativity estimate.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix Quasidiagonal
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

universe u

/-- **ucp matrix factorizations with only the left bimodule clause.**  This is
`IsMatrixCPAP` without the right bimodule clause and without both multiplicativity
clauses.  It is strictly smaller in proof content: `isMatrixCPAP_of_leftBimodule` rebuilds
the deleted clauses.  It is true for unital nuclear `A` (Choi--Effros and Choi's
inequality; see the module docstring). -/
def IsMatrixLeftBimoduleCPAP (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ (F : Finset A) (δ : ℝ), 0 < δ →
    ∃ (Y : FiniteModel) (ρ : A →ₗ[ℂ] Matrix Y Y ℂ) (ψ : Matrix Y Y ℂ →ₗ[ℂ] A),
      ρ 1 = 1 ∧ IsCompletelyPositiveOnMatrices Y ⇑ρ ∧ (∀ a : A, ‖ρ a‖ ≤ ‖a‖) ∧
      (∀ a : A, ρ (star a) = star (ρ a)) ∧
      ψ 1 = 1 ∧ (∀ v : Y → ℂ, ∃ c : A, ψ (vecMulVec v (star v)) = star c * c) ∧
      (∀ M : Matrix Y Y ℂ, ψ (star M) = star (ψ M)) ∧
      (∀ a ∈ F, ‖ψ (ρ a) - a‖ ≤ δ) ∧
      (∀ a ∈ F, ∀ M : Matrix Y Y ℂ, ‖ψ (ρ a * M) - a * ψ M‖ ≤ δ * ‖M‖)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.IsMatrixLeftBimoduleCPAP

/-- **One bimodule step.**  If `ψ` is left `u`-bimodular up to `δ`, `‖u‖ ≤ K`, `‖M‖ ≤ L`
and `ψ M ≈ c` up to `e`, then `ψ(ρ(u) M) ≈ u c` up to `δ L + K e`. -/
theorem norm_bimod_step {A : Type u} [CStarAlgebra A] {Y : FiniteModel}
    (ρ : A →ₗ[ℂ] Matrix Y Y ℂ) (ψ : Matrix Y Y ℂ →ₗ[ℂ] A) {u : A} {δ K L e : ℝ}
    (hu : ∀ M : Matrix Y Y ℂ, ‖ψ (ρ u * M) - u * ψ M‖ ≤ δ * ‖M‖) (hδ : 0 ≤ δ)
    (huK : ‖u‖ ≤ K) {M : Matrix Y Y ℂ} (hML : ‖M‖ ≤ L) {c : A} (hc : ‖ψ M - c‖ ≤ e) :
    ‖ψ (ρ u * M) - u * c‖ ≤ δ * L + K * e := by
  have e1 : ψ (ρ u * M) - u * c = (ψ (ρ u * M) - u * ψ M) + u * (ψ M - c) := by
    rw [mul_sub]
    abel
  rw [e1]
  calc ‖(ψ (ρ u * M) - u * ψ M) + u * (ψ M - c)‖
      ≤ ‖ψ (ρ u * M) - u * ψ M‖ + ‖u * (ψ M - c)‖ := norm_add_le _ _
    _ ≤ δ * ‖M‖ + ‖u‖ * ‖ψ M - c‖ := add_le_add (hu M) (norm_mul_le _ _)
    _ ≤ δ * L + K * e :=
        add_le_add (mul_le_mul_of_nonneg_left hML hδ)
          (mul_le_mul huK hc (norm_nonneg _) ((norm_nonneg u).trans huK))

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.norm_bimod_step

/-- **The first multiplicativity estimate.**  From left `a`-bimodularity, `ψρ(b) ≈ b` and
`ψρ(ab) ≈ ab`, the defect `ψ(ρ(ab) − ρ(a)ρ(b))` is at most `δ + (δK + Kδ)`. -/
theorem norm_psi_mul_defect_le {A : Type u} [CStarAlgebra A] {Y : FiniteModel}
    (ρ : A →ₗ[ℂ] Matrix Y Y ℂ) (ψ : Matrix Y Y ℂ →ₗ[ℂ] A) {a b : A} {δ K : ℝ}
    (hδ : 0 ≤ δ) (ha : ∀ M : Matrix Y Y ℂ, ‖ψ (ρ a * M) - a * ψ M‖ ≤ δ * ‖M‖)
    (haK : ‖a‖ ≤ K) (hRb : ‖ρ b‖ ≤ K) (hb : ‖ψ (ρ b) - b‖ ≤ δ)
    (hab : ‖ψ (ρ (a * b)) - a * b‖ ≤ δ) :
    ‖ψ (ρ (a * b) - ρ a * ρ b)‖ ≤ δ + (δ * K + K * δ) := by
  have step : ‖ψ (ρ a * ρ b) - a * b‖ ≤ δ * K + K * δ :=
    norm_bimod_step ρ ψ ha hδ haK hRb hb
  have e1 : ψ (ρ (a * b) - ρ a * ρ b)
      = (ψ (ρ (a * b)) - a * b) - (ψ (ρ a * ρ b) - a * b) := by
    rw [map_sub]
    abel
  rw [e1]
  calc ‖(ψ (ρ (a * b)) - a * b) - (ψ (ρ a * ρ b) - a * b)‖
      ≤ ‖ψ (ρ (a * b)) - a * b‖ + ‖ψ (ρ a * ρ b) - a * b‖ := norm_sub_le _ _
    _ ≤ δ + (δ * K + K * δ) := add_le_add hab step

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.norm_psi_mul_defect_le

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
