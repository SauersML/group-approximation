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

variable {A : Type u} [CStarAlgebra A]

/-- **The Kraus map of an amplification.**  For the column `G (i, s) = P s i`,
`ψ_G(N ⊗ 1) = ∑_{i,j} N_{ij} • ∑_s (P s i)⋆ (P s j)`. -/
theorem choiKraus_krausMap_amplify {k : ℕ} (P : Fin k → Fin k → A)
    (N : Matrix (Fin k) (Fin k) ℂ) :
    choiEffrosKrausMap (fun z : Fin k × Fin k ↦ P z.2 z.1) (choiKrausAmplifyLinear k N) =
      ∑ i : Fin k, ∑ j : Fin k, N i j • ∑ s : Fin k, star (P s i) * P s j := by
  have hinner : ∀ i s : Fin k,
      ∑ y' : Fin k × Fin k,
          Matrix.blockDiagonal (fun _ : Fin k ↦ N) (i, s) y' • P y'.2 y'.1 =
        ∑ j : Fin k, N i j • P s j := by
    intro i s
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.sum_eq_single s]
    · exact congrArg (· • P s j) (Matrix.blockDiagonal_apply_eq (fun _ : Fin k ↦ N) i j s)
    · intro t _ hts
      rw [Matrix.blockDiagonal_apply_ne _ i j (Ne.symm hts), zero_smul]
    · intro hs
      exact absurd (Finset.mem_univ s) hs
  show ∑ y : Fin k × Fin k, star (P y.2 y.1) *
      ∑ y' : Fin k × Fin k, Matrix.blockDiagonal (fun _ : Fin k ↦ N) y y' • P y'.2 y'.1 = _
  rw [Fintype.sum_prod_type]
  calc ∑ i : Fin k, ∑ s : Fin k, star (P (i, s).2 (i, s).1) *
        ∑ y' : Fin k × Fin k,
          Matrix.blockDiagonal (fun _ : Fin k ↦ N) (i, s) y' • P y'.2 y'.1
      = ∑ i : Fin k, ∑ s : Fin k, star (P s i) * ∑ j : Fin k, N i j • P s j := by
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
        exact congrArg (star (P s i) * ·) (hinner i s)
    _ = ∑ i : Fin k, ∑ s : Fin k, ∑ j : Fin k, N i j • (star (P s i) * P s j) := by
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ mul_smul_comm (N i j) (star (P s i)) (P s j)
    _ = ∑ i : Fin k, ∑ j : Fin k, ∑ s : Fin k, N i j • (star (P s i) * P s j) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        exact Finset.sum_comm
    _ = ∑ i : Fin k, ∑ j : Fin k, N i j • ∑ s : Fin k, star (P s i) * P s j := by
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.smul_sum]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiKraus_krausMap_amplify

/-- **Every cp map out of `M_k` is a Kraus-column map after amplification.**  For a
completely positive `ψ : M_k → A` with `k ≥ 1` there is a column `G : Fin k × Fin k → A`
with `ψ_G(N ⊗ 1) = ψ(N)` for every `N`. -/
theorem choiKraus_exists_column {k : ℕ} [Nonempty (Fin k)]
    (ψ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] A) (hψ : CStarExactness.IsCompletelyPositive ψ) :
    ∃ G : Fin k × Fin k → A, ∀ N : Matrix (Fin k) (Fin k) ℂ,
      choiEffrosKrausMap G (choiKrausAmplifyLinear k N) = ψ N := by
  obtain ⟨P, hP⟩ := BlackadarKirchberg.exists_factor_choiMatrix_of_cp ψ hψ
  have hentry : ∀ i j : Fin k,
      ψ (Matrix.single i j (1 : ℂ)) = ∑ s : Fin k, star (P s i) * P s j := by
    intro i j
    calc ψ (Matrix.single i j (1 : ℂ)) = BlackadarKirchberg.choiMatrix ψ i j :=
          (BlackadarKirchberg.choiMatrix_apply ψ i j).symm
      _ = (star P * P) i j := by rw [hP]
      _ = ∑ s : Fin k, (star P) i s * P s j := CStarExactness.cstarMatrix_mul_apply (star P) P i j
      _ = ∑ s : Fin k, star (P s i) * P s j := rfl
  refine ⟨fun z ↦ P z.2 z.1, fun N ↦ ?_⟩
  calc choiEffrosKrausMap (fun z : Fin k × Fin k ↦ P z.2 z.1) (choiKrausAmplifyLinear k N)
      = ∑ i : Fin k, ∑ j : Fin k, N i j • ∑ s : Fin k, star (P s i) * P s j :=
        choiKraus_krausMap_amplify (fun s i ↦ P s i) N
    _ = ∑ i : Fin k, ∑ j : Fin k, N i j • ψ (Matrix.single i j 1) := by
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        rw [hentry i j]
    _ = ψ (∑ i : Fin k, ∑ j : Fin k, N i j • Matrix.single i j 1) := by
        symm
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [map_sum]
        exact Finset.sum_congr rfl fun j _ ↦ map_smul ψ (N i j) (Matrix.single i j 1)
    _ = ψ N := congrArg ψ (BlackadarKirchberg.matrix_eq_sum_smul_single N).symm

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiKraus_exists_column

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
