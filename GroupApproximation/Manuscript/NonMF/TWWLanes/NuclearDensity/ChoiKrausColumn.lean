import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.ChoiEffrosKraus
import GroupApproximation.Analysis.BlackadarKirchbergFiniteDimensionalLift
import GroupApproximation.Analysis.CStarCompletelyPositiveForm
import GroupApproximation.Analysis.CStarExactness
import Mathlib.Data.Matrix.Block
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-34, part 1: every cp map `M_k → A` is a Kraus-column map after amplification

Let `ψ : M_k → A` be completely positive, with `k ≥ 1`.

1. The Choi matrix `C = [ψ(e_{ij})]` factors as `C = P⋆P` for some `P ∈ M_k(A)`
   (`BlackadarKirchberg.exists_factor_choiMatrix_of_cp`).
2. Put `G (i, s) = P s i` on `Fin k × Fin k`.  Let the amplification `N ↦ N ⊗ 1_k` be
   `Matrix.blockDiagonal (fun _ ↦ N)`.  Unwinding the block-diagonal sum gives
   `ψ_G(N ⊗ 1) = ∑_{i,j} N_{ij} • ∑_s (P s i)⋆ (P s j) = ∑_{i,j} N_{ij} • ψ(e_{ij}) = ψ(N)`.
3. The amplification is a unital `⋆`-homomorphism, so it is completely positive.

Everything in this file is proved.  No literature input is used; the argument is the
Choi-matrix computation, and every step is an identity.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

local instance choiKrausColumnMatrixCStarAlgebra (Z : Type) [Fintype Z] [DecidableEq Z]
    [Nonempty Z] : CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiKrausColumnMatrixCStarAlgebra

/-- The square model `Fin k × Fin k`, as a finite model. -/
abbrev choiKrausSquareModel (k : ℕ) : FiniteModel :=
  ⟨Fin k × Fin k, inferInstance, inferInstance⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiKrausSquareModel

/-- The amplification `N ↦ N ⊗ 1_k`, as the block-diagonal matrix with `k` copies of `N`. -/
def choiKrausAmplifyLinear (k : ℕ) :
    Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] Matrix (Fin k × Fin k) (Fin k × Fin k) ℂ where
  toFun N := Matrix.blockDiagonal fun _ : Fin k ↦ N
  map_add' N M := by
    show Matrix.blockDiagonal (fun _ : Fin k ↦ N + M) =
      Matrix.blockDiagonal (fun _ : Fin k ↦ N) + Matrix.blockDiagonal (fun _ : Fin k ↦ M)
    exact Matrix.blockDiagonal_add (fun _ : Fin k ↦ N) (fun _ : Fin k ↦ M)
  map_smul' c N := by
    show Matrix.blockDiagonal (fun _ : Fin k ↦ c • N) =
      c • Matrix.blockDiagonal (fun _ : Fin k ↦ N)
    exact Matrix.blockDiagonal_smul c (fun _ : Fin k ↦ N)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiKrausAmplifyLinear

/-- The amplification is unital. -/
theorem choiKraus_amplifyLinear_one (k : ℕ) : choiKrausAmplifyLinear k 1 = 1 := by
  show Matrix.blockDiagonal (fun _ : Fin k ↦ (1 : Matrix (Fin k) (Fin k) ℂ)) = 1
  exact Matrix.blockDiagonal_one

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiKraus_amplifyLinear_one

/-- The amplification is multiplicative. -/
theorem choiKraus_amplifyLinear_mul (k : ℕ) (N M : Matrix (Fin k) (Fin k) ℂ) :
    choiKrausAmplifyLinear k (N * M) =
      choiKrausAmplifyLinear k N * choiKrausAmplifyLinear k M := by
  show Matrix.blockDiagonal (fun _ : Fin k ↦ N * M) =
    Matrix.blockDiagonal (fun _ : Fin k ↦ N) * Matrix.blockDiagonal (fun _ : Fin k ↦ M)
  exact Matrix.blockDiagonal_mul (fun _ : Fin k ↦ N) (fun _ : Fin k ↦ M)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiKraus_amplifyLinear_mul

/-- The amplification, as a unital `⋆`-homomorphism. -/
def choiKrausAmplify (k : ℕ) :
    Matrix (Fin k) (Fin k) ℂ →⋆ₐ[ℂ] Matrix (Fin k × Fin k) (Fin k × Fin k) ℂ :=
  { AlgHom.ofLinearMap (choiKrausAmplifyLinear k) (choiKraus_amplifyLinear_one k)
      (choiKraus_amplifyLinear_mul k) with
    map_star' := fun N ↦ by
      show Matrix.blockDiagonal (fun _ : Fin k ↦ star N) =
        star (Matrix.blockDiagonal fun _ : Fin k ↦ N)
      exact (Matrix.blockDiagonal_conjTranspose (fun _ : Fin k ↦ N)).symm }

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiKrausAmplify

/-- The amplification is completely positive. -/
theorem choiKraus_isCompletelyPositive_amplifyLinear {k : ℕ} [Nonempty (Fin k)] :
    CStarExactness.IsCompletelyPositive (choiKrausAmplifyLinear k) := by
  have h := CStarExactness.isCompletelyPositive_of_starAlgHom
    (choiKrausAmplify k).toNonUnitalStarAlgHom
  exact h

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiKraus_isCompletelyPositive_amplifyLinear
