import GroupApproximation.Analysis.RationalStarPolynomialBlockDiagonal
import GroupApproximation.Analysis.ReducedProductMFDesignatedCoordinate

/-!
# The block-diagonal sequence in reduced-product MF permanence

At outer stage `n`, recursively block together the `n+1` designated inner
coordinates selected for the first `n+1` rational star polynomials.  Binary
block-diagonal norm identities give the manuscript's simultaneous upper and
lower polynomial estimates.  The generator matrices are uniformly bounded,
so they define elements of one norm-matrix corona.
-/

namespace GroupApproximation
namespace ReducedProductMFBlockDiagonal

open Filter
open PolarLiftingGeneralCStar
open RationalNoncommutativeStarPolynomial
open RationalStarPolynomialBlockDiagonal
open ReducedProductMFDiagonalData
open ReducedProductMFFiniteSelection
open NormMatrixCoronaPolynomialLifts
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u v

noncomputable local instance matrixBlockCStarAlgebraForReducedProductBlocks
    (Z : Type*) [Fintype Z] [DecidableEq Z] [Nonempty Z] :
    CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

noncomputable local instance boundedMatrixSequenceCStarAlgebraForReducedProductBlocks
    (X : ℕ → Type*) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
    [∀ n, Nonempty (X n)] : CStarAlgebra (BoundedMatrixSequence X) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

variable (B : ℕ → Type u) [∀ n, CStarAlgebra (B n)]
  [∀ n, Nontrivial (B n)]
variable {C : Type v} [CStarAlgebra C]
variable (i : C →⋆ₙₐ[ℂ] CStarProductCorona B cofinite)
variable (a : ℕ → C)
variable (hB : ∀ n, HasMFEmbedding (B n))

/-- The first `m+1` selected blocks at outer stage `n`. -/
def partialSelectedModel (n : ℕ) : (m : ℕ) → m ≤ n → FiniteModel
  | 0, _ => innerModel B hB n
      (designatedCoordinate B i a hB n ⟨0, Nat.zero_lt_succ n⟩)
  | m + 1, hm =>
      blockSumModel
        (partialSelectedModel n m (Nat.le_trans (Nat.le_succ m) hm))
        (innerModel B hB n
          (designatedCoordinate B i a hB n
            ⟨m + 1, Nat.lt_succ_of_le hm⟩))

theorem partialSelectedModel_nonempty (n : ℕ) :
  ∀ (m : ℕ) (hm : m ≤ n),
      Nonempty (partialSelectedModel B i a hB n m hm)
  | 0, _ => innerModelNonempty B hB n _
  | m + 1, hm =>
      Nonempty.elim
        (partialSelectedModel_nonempty n m
          (Nat.le_trans (Nat.le_succ m) hm)) fun x ↦
            ⟨Sum.inl x⟩

instance partialSelectedModelNonempty (n m : ℕ) (hm : m ≤ n) :
    Nonempty (partialSelectedModel B i a hB n m hm) :=
  partialSelectedModel_nonempty B i a hB n m hm

/-- The first `m+1` selected matrices for generator `j`. -/
def partialSelectedGenerator (n j : ℕ) :
    ∀ (m : ℕ) (hm : m ≤ n),
      Matrix (partialSelectedModel B i a hB n m hm)
        (partialSelectedModel B i a hB n m hm) ℂ
  | 0, _ => innerGeneratorLift B hB i a n j
      (designatedCoordinate B i a hB n ⟨0, Nat.zero_lt_succ n⟩)
  | m + 1, hm =>
      blockDiagMatrix
        (partialSelectedModel B i a hB n m
          (Nat.le_trans (Nat.le_succ m) hm))
        (innerModel B hB n
          (designatedCoordinate B i a hB n
            ⟨m + 1, Nat.lt_succ_of_le hm⟩))
        (partialSelectedGenerator n j m
          (Nat.le_trans (Nat.le_succ m) hm))
        (innerGeneratorLift B hB i a n j
          (designatedCoordinate B i a hB n
            ⟨m + 1, Nat.lt_succ_of_le hm⟩))

/-- The finite model at outer stage `n`. -/
def selectedModel (n : ℕ) : FiniteModel :=
  partialSelectedModel B i a hB n n le_rfl

instance selectedModelNonempty (n : ℕ) :
    Nonempty (selectedModel B i a hB n) :=
  partialSelectedModel_nonempty B i a hB n n le_rfl

/-- The block-diagonal matrix assigned to generator `j` at outer stage `n`. -/
def selectedGenerator (n j : ℕ) : Matrix (selectedModel B i a hB n)
    (selectedModel B i a hB n) ℂ :=
  partialSelectedGenerator B i a hB n j n le_rfl

theorem partialSelectedPolynomial_upper (n : ℕ) (r : Fin (n + 1)) :
    ∀ (m : ℕ) (hm : m ≤ n),
      ‖eval (fun j ↦ partialSelectedGenerator B i a hB n j m hm)
          (enumeration r)‖ <
        ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n)
          (enumeration r)‖ + stageError n
  | 0, _ => designatedCoordinate_upper B i a hB n r
      ⟨0, Nat.zero_lt_succ n⟩
  | m + 1, hm => by
      change
        ‖eval (fun j ↦ blockDiagMatrix _ _
          (partialSelectedGenerator B i a hB n j m
            (Nat.le_trans (Nat.le_succ m) hm))
          (innerGeneratorLift B hB i a n j
            (designatedCoordinate B i a hB n
              ⟨m + 1, Nat.lt_succ_of_le hm⟩))) (enumeration r)‖ < _
      rw [norm_eval_blockDiag, max_lt_iff]
      exact ⟨partialSelectedPolynomial_upper n r m
          (Nat.le_trans (Nat.le_succ m) hm),
        designatedCoordinate_upper B i a hB n r
          ⟨m + 1, Nat.lt_succ_of_le hm⟩⟩

theorem designatedBlock_le_partialPolynomial (n : ℕ) (p : Polynomial)
    (s : Fin (n + 1)) :
    ∀ (m : ℕ) (hm : m ≤ n), s.val ≤ m →
      ‖eval (fun j ↦ innerGeneratorLift B hB i a n j
          (designatedCoordinate B i a hB n s)) p‖ ≤
        ‖eval (fun j ↦ partialSelectedGenerator B i a hB n j m hm) p‖
  | 0, _, hs => by
      have hs0 : s = ⟨0, Nat.zero_lt_succ n⟩ := by
        apply Fin.ext
        exact Nat.eq_zero_of_le_zero hs
      subst s
      exact le_rfl
  | m + 1, hm, hs => by
      change _ ≤
        ‖eval (fun j ↦ blockDiagMatrix _ _
          (partialSelectedGenerator B i a hB n j m
            (Nat.le_trans (Nat.le_succ m) hm))
          (innerGeneratorLift B hB i a n j
            (designatedCoordinate B i a hB n
              ⟨m + 1, Nat.lt_succ_of_le hm⟩))) p‖
      rw [norm_eval_blockDiag]
      by_cases hnew : s.val = m + 1
      · have hsnew : s = ⟨m + 1, Nat.lt_succ_of_le hm⟩ := by
          apply Fin.ext
          exact hnew
        subst s
        exact le_max_right _ _
      · apply le_trans
        · exact designatedBlock_le_partialPolynomial n p s m
            (Nat.le_trans (Nat.le_succ m) hm) (by omega)
        · exact le_max_left _ _

theorem selectedPolynomial_upper (n : ℕ) (r : Fin (n + 1)) :
    ‖eval (selectedGenerator B i a hB n) (enumeration r)‖ <
      ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n)
        (enumeration r)‖ + stageError n :=
  partialSelectedPolynomial_upper B i a hB n r n le_rfl

theorem selectedPolynomial_lower (n : ℕ) (r : Fin (n + 1)) :
    ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n)
        (enumeration r)‖ - stageError n <
      ‖eval (selectedGenerator B i a hB n) (enumeration r)‖ := by
  exact (designatedCoordinate_lower B i a hB n r).trans_le
    (designatedBlock_le_partialPolynomial B i a hB n (enumeration r) r n
      le_rfl (Nat.le_of_lt_succ r.isLt))

theorem norm_innerGenerator_le_global (n j k : ℕ) :
    ‖innerGeneratorLift B hB i a n j k‖ ≤
      ‖reducedProductGeneratorLift B i a j‖ + 1 := by
  have hcoord := boundedMatrixSequence_coord_norm_le
    (fun r ↦ innerModel B hB n r) (innerGeneratorLift B hB i a n j) k
  have hlift := norm_generatorLift_lt
    (fun r ↦ innerModel B hB n r) (innerEmbedding B hB n)
    (fun q ↦ reducedProductGeneratorLift B i a q n) j
  calc
    ‖innerGeneratorLift B hB i a n j k‖ ≤
        ‖innerGeneratorLift B hB i a n j‖ := hcoord
    _ ≤ ‖innerEmbedding B hB n (reducedProductGeneratorLift B i a j n)‖ + 1 :=
      le_of_lt hlift
    _ = ‖reducedProductGeneratorLift B i a j n‖ + 1 := by
      rw [NonUnitalStarAlgHom.norm_map (innerEmbedding B hB n)
        (innerEmbedding_injective B hB n)]
    _ ≤ ‖reducedProductGeneratorLift B i a j‖ + 1 :=
      add_le_add (boundedCStarSequence_coord_norm_le B
        (reducedProductGeneratorLift B i a j) n) le_rfl

theorem norm_partialSelectedGenerator_le (n j : ℕ) :
    ∀ (m : ℕ) (hm : m ≤ n),
      ‖partialSelectedGenerator B i a hB n j m hm‖ ≤
        ‖reducedProductGeneratorLift B i a j‖ + 1
  | 0, _ => norm_innerGenerator_le_global B i a hB n j _
  | m + 1, hm => by
      change
        ‖blockDiagMatrix
          (partialSelectedModel B i a hB n m
            (Nat.le_trans (Nat.le_succ m) hm))
          (innerModel B hB n
            (designatedCoordinate B i a hB n
              ⟨m + 1, Nat.lt_succ_of_le hm⟩))
          (partialSelectedGenerator B i a hB n j m
            (Nat.le_trans (Nat.le_succ m) hm))
          (innerGeneratorLift B hB i a n j
            (designatedCoordinate B i a hB n
              ⟨m + 1, Nat.lt_succ_of_le hm⟩))‖ ≤ _
      rw [l2_opNorm_blockDiag, max_le_iff]
      exact ⟨norm_partialSelectedGenerator_le n j m
          (Nat.le_trans (Nat.le_succ m) hm),
        norm_innerGenerator_le_global B i a hB n j _⟩

/-- The selected generator matrices form a bounded matrix sequence. -/
def diagonalGenerator (j : ℕ) :
    BoundedMatrixSequence (fun n ↦ selectedModel B i a hB n) :=
  ⟨fun n ↦ selectedGenerator B i a hB n j,
    memℓp_infty ⟨‖reducedProductGeneratorLift B i a j‖ + 1, by
      rintro _ ⟨n, rfl⟩
      exact norm_partialSelectedGenerator_le B i a hB n j n le_rfl⟩⟩

theorem eval_diagonalGenerator_apply (p : Polynomial) (n : ℕ) :
    eval (diagonalGenerator B i a hB) p n =
      eval (selectedGenerator B i a hB n) p := by
  induction p with
  | zero => rfl
  | generator j => rfl
  | smul q p hp =>
      rw [eval_smul, eval_smul, lp.coeFn_smul, Pi.smul_apply, hp]
  | add p q hp hq =>
      rw [eval_add, eval_add, lp.coeFn_add, Pi.add_apply, hp, hq]
  | mul p q hp hq =>
      rw [eval_mul, eval_mul, lp.infty_coeFn_mul, Pi.mul_apply, hp, hq]
  | star p hp =>
      rw [eval_star, eval_star, lp.coeFn_star, Pi.star_apply, hp]

end

end ReducedProductMFBlockDiagonal
end GroupApproximation
