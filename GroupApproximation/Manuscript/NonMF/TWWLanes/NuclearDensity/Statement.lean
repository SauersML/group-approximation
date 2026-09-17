import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.Glue
import GroupApproximation.Analysis.CStarExactness
import Mathlib.Analysis.CStarAlgebra.Matrix
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-12, part 1: the τ-free gap behind approximately invariant densities

## Truth check: the lanes-file hypothesis of nm-tww-11 is FALSE as printed

The lanes file states the nm-tww-11 hypothesis with a ⋆-homomorphism `π : A →⋆ₐ B(H)`
and `H` finite-dimensional.  Read literally, nm-tww-12 is then **false**.  The CAR algebra
`M_{2^∞}` is separable, nuclear and simple, with a faithful trace, but it has no nonzero
finite-dimensional representation.  Brown--Ozawa, Thm 6.2.7(4) uses an infinite-dimensional
`H` with a finite-rank density.  The **corrected, true** interface is the one already on
disk: `NuclearAmenable.HasApproxInvariantDensities` (NuclearAmenable/Glue.lean).  It uses a
**ucp** map into matrices, a Hermitian `T` with `tr(T²) = 1`, the vector-state trace clause,
the Hilbert--Schmidt commutator and weighted multiplicativity.  This lane targets
`NuclearAmenable.NuclearTraceApproxDensityStatement` in that form.

## The gap, and why it is true

`NuclearDensityGapStatement` has two **τ-free** fields.

* `cpap`: a unital nuclear `A` has ucp factorizations `ψ ∘ ρ ≈ id` through matrix algebras.
  The approximate-bimodule clauses are included.  This is true.  Brown--Ozawa, Prop 2.2.6
  gives ucp `α : A → D`, `β : D → A` through a finite-dimensional `D`.  Embed
  `D ≅ ⊕ M_{kᵢ} ⊆ M_Y` unitally, and set `ρ = ι ∘ α` and `ψ = β ∘ E`, where `E` is the
  conditional expectation.  Then `ψ` is ucp, so it is positive, ⋆-preserving and
  contractive.  Choose the approximation on `F ∪ F⋆F ∪ FF⋆ ∪ F·F ∪ …`.  Kadison--Schwarz for
  `ρ` and Choi's Cauchy--Schwarz inequality for `ψ` then give
  `‖ψ(ρ(a)M) − aψ(M)‖ ≤ δ‖M‖`, and symmetrically on the other side.  Expanding the products
  gives the last two clauses.
* `sqrtControl`: Powers--Størmer with a Halmos dilation, which is matrix analysis.  Write
  each `x ∈ F` as a combination of four unitaries (`CStarAlgebra.exists_sum_four_unitary`),
  and let `F'` contain them, their adjoints and `1`.  For a unitary `u`, put `y = ρ u` and
  take the unitary dilation `U` of `y`.  Powers--Størmer, `‖√P − √Q‖₂² ≤ ‖P − Q‖₁`, applied
  to `P = h ⊕ 0` and `Q = UPU*` gives `‖[√h, y]‖₂² ≤ ‖[h,y]‖₁ + 3·tr(h(1−yy*))^{1/2}`
  `+ tr(h(1−y*y))`.  The hypotheses bound every term by `O(√η)`.  Linearity and the
  triangle inequality in `‖·‖₂` finish the argument with `T = √h`.

**Strictly smaller in proof content.**  Neither field mentions a trace.  All of the
τ-dependent work is **proved** in `Reduction`: building the density of `τ ∘ ψ`, its
positivity and hermiticity (polarization for tracial states), `tr h = 1`, and the three
trace identities with cyclicity.  The same file derives the commutator hypothesis from
traciality and the bimodule clauses.  Separability and faithfulness are never used.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix Quasidiagonal
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

universe u

/-- **ucp matrix factorizations with approximate bimodule clauses.**  For every finite `F`
and `δ > 0` there are a ucp `ρ : A → M_Y` and a unital positive contraction
`ψ : M_Y → A` that preserves stars, with `ψ ρ ≈ id` on `F`.  Also, `ψ` is approximately
`F`-bimodular against `ρ`, and its multiplicative defects on `F × F` are small. -/
def IsMatrixCPAP (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ (F : Finset A) (δ : ℝ), 0 < δ →
    ∃ (Y : FiniteModel) (ρ : A →ₗ[ℂ] Matrix Y Y ℂ) (ψ : Matrix Y Y ℂ →ₗ[ℂ] A),
      ρ 1 = 1 ∧ IsCompletelyPositiveOnMatrices Y ⇑ρ ∧ (∀ a : A, ‖ρ a‖ ≤ ‖a‖) ∧
      (∀ a : A, ρ (star a) = star (ρ a)) ∧
      ψ 1 = 1 ∧ (∀ v : Y → ℂ, ∃ c : A, ψ (vecMulVec v (star v)) = star c * c) ∧
      (∀ M : Matrix Y Y ℂ, ψ (star M) = star (ψ M)) ∧
      (∀ a ∈ F, ‖ψ (ρ a) - a‖ ≤ δ) ∧
      (∀ a ∈ F, ∀ M : Matrix Y Y ℂ,
        ‖ψ (ρ a * M) - a * ψ M‖ ≤ δ * ‖M‖ ∧ ‖ψ (M * ρ a) - ψ M * a‖ ≤ δ * ‖M‖) ∧
      (∀ a ∈ F, ∀ b ∈ F, ‖ψ (ρ (a * b) - ρ a * ρ b)‖ ≤ δ) ∧
      (∀ a ∈ F, ∀ b ∈ F,
        ‖ψ (star (ρ (a * b) - ρ a * ρ b) * (ρ (a * b) - ρ a * ρ b))‖ ≤ δ)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.IsMatrixCPAP

/-- **Square roots of approximately invariant densities commute in `‖·‖₂`.**  Given `F`
and `ε`, there are a finite `F'` and an `η > 0` with the following property.  Take any
unital, contractive, ⋆-preserving linear `ρ` into matrices and any density `h`
(`h ≥ 0`, `tr h = 1`).  Suppose `h` commutes with `ρ(F')` up to `η` in trace norm, stated
dually, and `ρ` is `h`-weakly multiplicative on `F'` up to `η`.  Then some Hermitian
square root `T` of `h` commutes with `ρ(F)` up to `ε` in squared unnormalized
Hilbert--Schmidt norm.  The module docstring explains why this holds. -/
def HasSqrtCommutatorControl (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ (F : Finset A) (ε : ℝ), 0 < ε →
    ∃ (F' : Finset A) (η : ℝ), 0 < η ∧
      ∀ (Y : FiniteModel) (ρ : A →ₗ[ℂ] Matrix Y Y ℂ),
        ρ 1 = 1 → (∀ a : A, ‖ρ a‖ ≤ ‖a‖) → (∀ a : A, ρ (star a) = star (ρ a)) →
        ∀ h : Matrix Y Y ℂ, h.PosSemidef → Matrix.trace h = 1 →
          (∀ a ∈ F', ∀ x : Matrix Y Y ℂ,
            ‖Matrix.trace ((h * ρ a - ρ a * h) * x)‖ ≤ η * ‖x‖) →
          (∀ a ∈ F', ∀ b ∈ F', ‖Matrix.trace (h * (ρ (a * b) - ρ a * ρ b))‖ ≤ η) →
          ∃ T : Matrix Y Y ℂ, T.IsHermitian ∧ T * T = h ∧
            ∀ x ∈ F, (Matrix.trace ((ρ x * T - T * ρ x)ᴴ * (ρ x * T - T * ρ x))).re ≤ ε

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.HasSqrtCommutatorControl

/-- **The single remaining gap of lane nm-tww-12.**  It is τ-free: nuclear algebras have ucp
matrix factorizations with approximate bimodule clauses (Brown--Ozawa 2.2.6 + Choi), and
square roots of approximately invariant densities commute in Hilbert--Schmidt norm
(Powers--Størmer).  Both are true.  See the module docstring. -/
structure NuclearDensityGapStatement : Prop where
  /-- Nuclear unital algebras have ucp matrix factorizations with bimodule clauses. -/
  cpap : ∀ (A : Type u) (_ : CStarAlgebra A),
    CStarExactness.IsNuclearCStarAlgebra A → IsMatrixCPAP A
  /-- Powers--Størmer control of square roots, on every unital C⋆-algebra. -/
  sqrtControl : ∀ (A : Type u) (_ : CStarAlgebra A), HasSqrtCommutatorControl A

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.NuclearDensityGapStatement

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
