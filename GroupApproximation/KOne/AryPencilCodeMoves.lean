import GroupApproximation.KOne.AryPencilEntry
import GroupApproximation.KOne.AryPrefixCodes
import GroupApproximation.KOne.FieldMatrixReduction
import GroupApproximation.Meta.AxiomGuard

/-!
# Scalar moves along complete prefix codes, at arbitrary arity

The binary development transports scalar matrices along mixed-depth complete prefix codes
(`KOne/CodeScalarMoves.lean`) and proves the transported units lie in the class group by a
transvection/diagonal decomposition carried out by hand.  At arity `d` the transport along a
complete code `D` is the scalar embedding of the complete family `F.codeFamily D`, so its
units are central scalars modulo the stably elementary units by
`CompleteMatrixFamily.unitsEquiv_field_matrix_mem_centralClassGroup`, with no computation
(`codeScalar_unit_mem`).  The module also carries the value-level action of scalar moves on
code pencils (`KOne/PencilEntryArith.lean`): multiplying a code-pencil value by a transported
scalar matrix multiplies the coefficient matrices.
-/

namespace GroupApproximation
namespace CompleteMatrixFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)
variable {k : Type*} [Field k] [Algebra k A]

/-- Scalar-matrix transport along a prefix code. -/
noncomputable def codeScalar {κ : Type*} [Fintype κ] (D : AryPrefixCode κ ι)
    (G : Matrix κ κ k) : A :=
  ∑ i, ∑ j, F.wordS (D.word i) * algebraMap k A (G i j) * F.wordT (D.word j)

/-- **Scalar moves along complete codes are central scalars modulo the stably elementary
units.**  No invertibility hypothesis on `G` is needed: the unit `u` supplies it. -/
theorem codeScalar_unit_mem [Nontrivial A] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (D : AryPrefixCode κ ι) (hD : F.IsComplete D) (G : Matrix κ κ k) (u : Aˣ)
    (hu : (u : A) = F.codeScalar D G) :
    u ∈ centralClassGroup A := by
  have hval : (((F.codeFamily D hD).unitsEquiv.symm u : (Matrix κ κ A)ˣ) : Matrix κ κ A) =
      (F.codeFamily D hD).matrixRingEquiv.symm (u : A) := rfl
  have hU : (((F.codeFamily D hD).unitsEquiv.symm u : (Matrix κ κ A)ˣ) : Matrix κ κ A) =
      (algebraMap k A).mapMatrix G := by
    rw [hval, hu]
    apply (F.codeFamily D hD).matrixRingEquiv.injective
    rw [RingEquiv.apply_symm_apply]
    rfl
  have hmem := (F.codeFamily D hD).unitsEquiv_field_matrix_mem_centralClassGroup hdiv
    (algebraMap k A) (fun r x ↦ Algebra.commutes r x) G _ hU
  rwa [MulEquiv.apply_symm_apply] at hmem

theorem codeScalar_one {κ : Type*} [Fintype κ] [DecidableEq κ] (D : AryPrefixCode κ ι)
    (hD : F.IsComplete D) : F.codeScalar (k := k) D 1 = 1 := by
  classical
  unfold codeScalar
  calc ∑ i, ∑ j, F.wordS (D.word i) * algebraMap k A ((1 : Matrix κ κ k) i j) *
        F.wordT (D.word j)
      = ∑ i, ∑ j, (if i = j then F.wordS (D.word i) * F.wordT (D.word j) else 0) := by
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Matrix.one_apply, apply_ite (algebraMap k A), map_one, map_zero]
        simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    _ = ∑ i, F.wordS (D.word i) * F.wordT (D.word i) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
    _ = 1 := hD

theorem codeScalar_mul {κ : Type*} [Fintype κ] [DecidableEq κ] (D : AryPrefixCode κ ι)
    (G G' : Matrix κ κ k) :
    F.codeScalar (k := k) D G * F.codeScalar (k := k) D G' =
      F.codeScalar (k := k) D (G * G') := by
  classical
  have h := F.codePair_mul D D.word D.word (fun i j ↦ algebraMap k A (G i j))
    (fun j l ↦ algebraMap k A (G' j l))
  beta_reduce at h
  unfold codeScalar
  rw [h]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  congr 1
  congr 1
  rw [Matrix.mul_apply, map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ (map_mul _ _ _).symm

/-- **Right scalar move on a code pencil**: multiplying by a transported scalar matrix along
the column code multiplies the coefficient matrices on the right. -/
theorem pencilVal_mul_codeScalar {ρ κ : Type*} [Fintype ρ] [Fintype κ] [DecidableEq κ]
    (R : AryPrefixCode ρ ι) (C : AryPrefixCode κ ι)
    (Ac Bc : ρ → κ → ι → k) (Cm : ρ → κ → k) (G : Matrix κ κ k) :
    (∑ i, ∑ j, F.wordS (R.word i) * F.pencilEntry (Ac i j) (Bc i j) (Cm i j) *
        F.wordT (C.word j)) * F.codeScalar (k := k) C G =
    ∑ i, ∑ j, F.wordS (R.word i) *
      F.pencilEntry (fun r ↦ ∑ l, Ac i l r * G l j) (fun r ↦ ∑ l, Bc i l r * G l j)
        (∑ l, Cm i l * G l j) * F.wordT (C.word j) := by
  classical
  have h := F.codePair_mul C R.word C.word
    (fun i l ↦ F.pencilEntry (Ac i l) (Bc i l) (Cm i l))
    (fun l j ↦ algebraMap k A (G l j))
  beta_reduce at h
  unfold codeScalar
  rw [h]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
  congr 1
  calc ∑ l, F.pencilEntry (Ac i l) (Bc i l) (Cm i l) * algebraMap k A (G l j)
      = ∑ l, F.pencilEntry (fun r ↦ Ac i l r * G l j) (fun r ↦ Bc i l r * G l j)
          (Cm i l * G l j) :=
        Finset.sum_congr rfl fun l _ ↦ F.pencilEntry_mul_algebraMap _ _ _ _
    _ = _ := F.sum_pencilEntry Finset.univ _ _ _

/-- **Left scalar move on a code pencil.** -/
theorem codeScalar_mul_pencilVal {ρ κ : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype κ]
    (R : AryPrefixCode ρ ι) (C : AryPrefixCode κ ι)
    (Ac Bc : ρ → κ → ι → k) (Cm : ρ → κ → k) (G : Matrix ρ ρ k) :
    F.codeScalar (k := k) R G *
      (∑ i, ∑ j, F.wordS (R.word i) * F.pencilEntry (Ac i j) (Bc i j) (Cm i j) *
        F.wordT (C.word j)) =
    ∑ i, ∑ j, F.wordS (R.word i) *
      F.pencilEntry (fun r ↦ ∑ l, G i l * Ac l j r) (fun r ↦ ∑ l, G i l * Bc l j r)
        (∑ l, G i l * Cm l j) * F.wordT (C.word j) := by
  classical
  have h := F.codePair_mul R R.word C.word (fun i l ↦ algebraMap k A (G i l))
    (fun l j ↦ F.pencilEntry (Ac l j) (Bc l j) (Cm l j))
  beta_reduce at h
  unfold codeScalar
  rw [h]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
  congr 1
  calc ∑ l, algebraMap k A (G i l) * F.pencilEntry (Ac l j) (Bc l j) (Cm l j)
      = ∑ l, F.pencilEntry (fun r ↦ G i l * Ac l j r) (fun r ↦ G i l * Bc l j r)
          (G i l * Cm l j) :=
        Finset.sum_congr rfl fun l _ ↦ F.algebraMap_mul_pencilEntry _ _ _ _
    _ = _ := F.sum_pencilEntry Finset.univ _ _ _

end CompleteMatrixFamily
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.codeScalar_unit_mem
#audit_axioms GroupApproximation.CompleteMatrixFamily.codeScalar_mul
#audit_axioms GroupApproximation.CompleteMatrixFamily.pencilVal_mul_codeScalar
#audit_axioms GroupApproximation.CompleteMatrixFamily.codeScalar_mul_pencilVal
