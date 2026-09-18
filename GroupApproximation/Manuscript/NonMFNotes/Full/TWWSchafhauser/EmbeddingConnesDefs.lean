import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.LocalAmenable
import GroupApproximation.Analysis.CStarExactness
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Connes' trick, the interfaces: densities, matrix CPAP, square-root control

Lane TWWSch3b1 (work order WO-TWWSch-3b-1).  Manuscript: `non_mf_group_notes.tex`, the
Tikuisis--White--Winter input "every faithful trace on a separable nuclear C⋆-algebra is
amenable" (Schafhauser's proof, §3, uses it through the tracial embedding of 3b).
Source: Brown--Ozawa, *C⋆-algebras and finite-dimensional approximations*, Thm 6.2.7
(Connes' trick), Prop 2.2.6, and Powers--Størmer (1970).

This file only holds definitions; the proofs are in the other `EmbeddingConnes*` files.
The definitions are local adaptations of those of the foreign `NuclearAmenable.Glue`,
`NuclearDensity.Statement` and `NuclearDensity.CloseCPAP`, `CloseSqrt` modules (never wired,
partly WIP), restated here so that this lane can prove them without importing those.

* `HasApproxInvariantDensities τ`: ucp matrix models with a Hilbert--Schmidt density `T`
  that is almost invariant and almost multiplicative.
* `IsMatrixCPAP A`, `IsMatrixLeftBimoduleCPAP A`: ucp matrix factorizations with approximate
  bimodule clauses.
* `HasSqrtCommutatorControl A`, `ContractionSqrtCommutatorControl`: Powers--Størmer
  control of square roots of approximately invariant densities.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open Matrix Quasidiagonal
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

universe u

/-- **Approximately invariant densities for `τ`.**  For every finite `F` and `ε > 0` there
is a ucp map `φ` into a matrix algebra and a Hermitian `T` with `tr(T²) = 1` (unnormalized
trace) such that, on `F` up to `ε`: `‖τ x − tr(T φ(x) T)‖`, `‖φ(x) T − T φ(x)‖₂²` and
`‖(φ(xy) − φ(x)φ(y)) T‖₂²` are small (`‖M‖₂² = re tr(Mᴴ M)`). -/
def HasApproxInvariantDensities {A : Type u} [CStarAlgebra A] (τ : A → ℂ) : Prop :=
  ∀ (F : Finset A) (ε : ℝ), 0 < ε →
    ∃ (Y : FiniteModel) (φ : A →ₗ[ℂ] Matrix Y Y ℂ) (T : Matrix Y Y ℂ),
      φ 1 = 1 ∧ IsCompletelyPositiveOnMatrices Y ⇑φ ∧ T.IsHermitian ∧
      Matrix.trace (T * T) = 1 ∧
      (∀ x ∈ F, ‖τ x - Matrix.trace (T * φ x * T)‖ ≤ ε) ∧
      (∀ x ∈ F, (Matrix.trace ((φ x * T - T * φ x)ᴴ * (φ x * T - T * φ x))).re ≤ ε) ∧
      (∀ x ∈ F, ∀ y ∈ F,
        (Matrix.trace (((φ (x * y) - φ x * φ y) * T)ᴴ *
          ((φ (x * y) - φ x * φ y) * T))).re ≤ ε)

/-- **ucp matrix factorizations with approximate bimodule clauses.**  For every finite `F`
and `δ > 0` there are a ucp `ρ : A → M_Y` and a unital, positive, star-preserving
`ψ : M_Y → A` with `ψ ρ ≈ id` on `F`, `ψ` approximately `F`-bimodular against `ρ`, and small
multiplicative defects on `F × F`. -/
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

/-- **ucp matrix factorizations with only the left bimodule clause.**  This is
`IsMatrixCPAP` without the right bimodule clause and the two multiplicativity clauses,
which are rebuilt in `EmbeddingConnesCPAP`.  True for unital nuclear `A` (Choi--Effros
perturbation of a cpc factorization through a finite-dimensional algebra, and Choi's
Cauchy--Schwarz inequality). -/
def IsMatrixLeftBimoduleCPAP (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ (F : Finset A) (δ : ℝ), 0 < δ →
    ∃ (Y : FiniteModel) (ρ : A →ₗ[ℂ] Matrix Y Y ℂ) (ψ : Matrix Y Y ℂ →ₗ[ℂ] A),
      ρ 1 = 1 ∧ IsCompletelyPositiveOnMatrices Y ⇑ρ ∧ (∀ a : A, ‖ρ a‖ ≤ ‖a‖) ∧
      (∀ a : A, ρ (star a) = star (ρ a)) ∧
      ψ 1 = 1 ∧ (∀ v : Y → ℂ, ∃ c : A, ψ (vecMulVec v (star v)) = star c * c) ∧
      (∀ M : Matrix Y Y ℂ, ψ (star M) = star (ψ M)) ∧
      (∀ a ∈ F, ‖ψ (ρ a) - a‖ ≤ δ) ∧
      (∀ a ∈ F, ∀ M : Matrix Y Y ℂ, ‖ψ (ρ a * M) - a * ψ M‖ ≤ δ * ‖M‖)

/-- **Square roots of approximately invariant densities commute in `‖·‖₂`.**  Given `F`
and `ε`, there are a finite `F'` and `η > 0` such that for every unital, contractive,
star-preserving linear `ρ` into matrices and every density `h ≥ 0`, `tr h = 1`, which
commutes with `ρ(F')` up to `η` in trace norm (stated dually) and for which `ρ` is
`h`-weakly multiplicative on `F'` up to `η`, some Hermitian square root `T` of `h`
commutes with `ρ(F)` up to `ε` in squared unnormalized Hilbert--Schmidt norm. -/
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

/-- **Powers--Størmer control for one contraction.**  For every `ε > 0` there is `η > 0`
such that for a contraction `y` and `T ≥ 0` with `T² = h`, `tr h = 1`, `h` commuting with
`y` up to `η` in trace norm (stated dually), and `|tr(h(1 − y⋆y))|, |tr(h(1 − yy⋆))| ≤ η`,
one has `‖yT − Ty‖₂² ≤ ε`.  True with `η = min(ε/2, ε²/16)` by the Halmos dilation
`U = [[y, (1 − yy⋆)^{1/2}], [(1 − y⋆y)^{1/2}, −y⋆]]` and Powers--Størmer
`‖√P − √Q‖₂² ≤ ‖P − Q‖₁` applied to `P = h ⊕ 0`, `Q = U P U⋆`. -/
def ContractionSqrtCommutatorControl : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
    ∀ (Y : FiniteModel) (y h T : Matrix Y Y ℂ), ‖y‖ ≤ 1 → T.PosSemidef → T * T = h →
      Matrix.trace h = 1 →
      (∀ x : Matrix Y Y ℂ, ‖Matrix.trace ((h * y - y * h) * x)‖ ≤ η * ‖x‖) →
      ‖Matrix.trace (h * (1 - star y * y))‖ ≤ η →
      ‖Matrix.trace (h * (1 - y * star y))‖ ≤ η →
      (Matrix.trace ((y * T - T * y)ᴴ * (y * T - T * y))).re ≤ ε

end

end GroupApproximation.Full.TWWSchafhauser
