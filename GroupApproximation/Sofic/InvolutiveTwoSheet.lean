import GroupApproximation.Sofic.HyperlinearAmplification
import Mathlib.Data.Matrix.Block

/-!
# The two-sheet matrix model of an involutive extension

An involutive automorphism is spatialized by doubling a matrix model.  The
old element `q` acts as `diag(U_q, U_(psi q))`, while the new order-two
generator exchanges the two sheets.  This file records the exact block
identities used by the hyperlinear finite-extension argument.

The construction is deliberately independent of a particular group.  Its
application is the finite star-synchronizing extension in the Leavitt-atlas
program: adjoining the sheet swap does not create an additional tracial
approximation hypothesis.
-/

namespace GroupApproximation

open Matrix

/-- Two copies of one finite matrix model. -/
abbrev twoSheetModel (Y : FiniteModel) : FiniteModel :=
  ⟨Y ⊕ Y, inferInstance, inferInstance⟩

@[simp] theorem card_twoSheetModel (Y : FiniteModel) :
    Fintype.card (twoSheetModel Y) = 2 * Fintype.card Y := by
  show Fintype.card (Y ⊕ Y) = _
  rw [Fintype.card_sum]
  ring

/-- A matrix and its involutive mate on the two diagonal sheets. -/
def twoSheetDiagonal (Y : FiniteModel) (A B : Matrix Y Y ℂ) :
    Matrix (Y ⊕ Y) (Y ⊕ Y) ℂ :=
  Matrix.fromBlocks A 0 0 B

/-- The unitary which exchanges the two sheets. -/
def twoSheetSwap (Y : FiniteModel) : Matrix (Y ⊕ Y) (Y ⊕ Y) ℂ :=
  Matrix.fromBlocks 0 1 1 0

theorem twoSheetDiagonal_mul (Y : FiniteModel)
    (A B C D : Matrix Y Y ℂ) :
    twoSheetDiagonal Y A B * twoSheetDiagonal Y C D =
      twoSheetDiagonal Y (A * C) (B * D) := by
  unfold twoSheetDiagonal
  rw [Matrix.fromBlocks_multiply]
  congr 1 <;> simp

theorem twoSheetDiagonal_one (Y : FiniteModel) :
    twoSheetDiagonal Y (1 : Matrix Y Y ℂ) 1 = 1 := by
  unfold twoSheetDiagonal
  exact Matrix.fromBlocks_one

theorem twoSheetDiagonal_conjTranspose (Y : FiniteModel)
    (A B : Matrix Y Y ℂ) :
    (twoSheetDiagonal Y A B)ᴴ = twoSheetDiagonal Y Aᴴ Bᴴ := by
  unfold twoSheetDiagonal
  rw [Matrix.fromBlocks_conjTranspose]
  congr 1 <;> simp

theorem twoSheetSwap_sq (Y : FiniteModel) :
    twoSheetSwap Y * twoSheetSwap Y = 1 := by
  unfold twoSheetSwap
  rw [Matrix.fromBlocks_multiply]
  simpa using (Matrix.fromBlocks_one :
    Matrix.fromBlocks (1 : Matrix Y Y ℂ) 0 0 1 = 1)

theorem twoSheetSwap_conjTranspose (Y : FiniteModel) :
    (twoSheetSwap Y)ᴴ = twoSheetSwap Y := by
  unfold twoSheetSwap
  rw [Matrix.fromBlocks_conjTranspose]
  congr 1 <;> simp

theorem twoSheetSwap_mem_unitaryGroup (Y : FiniteModel) :
    twoSheetSwap Y ∈ Matrix.unitaryGroup (Y ⊕ Y) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    twoSheetSwap_conjTranspose, twoSheetSwap_sq]

/-- Conjugating by the sheet swap exchanges the two diagonal blocks. -/
theorem twoSheetSwap_conj_diagonal (Y : FiniteModel)
    (A B : Matrix Y Y ℂ) :
    twoSheetSwap Y * twoSheetDiagonal Y A B * twoSheetSwap Y =
      twoSheetDiagonal Y B A := by
  unfold twoSheetSwap twoSheetDiagonal
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 1 <;> simp

theorem twoSheetDiagonal_mem_unitaryGroup (Y : FiniteModel)
    {A B : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ)
    (hB : B ∈ Matrix.unitaryGroup Y ℂ) :
    twoSheetDiagonal Y A B ∈ Matrix.unitaryGroup (Y ⊕ Y) ℂ := by
  have hA' : A * Aᴴ = 1 := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hA
    exact hA
  have hB' : B * Bᴴ = 1 := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hB
    exact hB
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    twoSheetDiagonal_conjTranspose, twoSheetDiagonal_mul, hA', hB',
    twoSheetDiagonal_one]

/-- The normalized trace of a doubled diagonal is the average of the two
normalized traces. -/
theorem normTrace_twoSheetDiagonal (Y : FiniteModel)
    (hY : 0 < Fintype.card Y) (A B : Matrix Y Y ℂ) :
    normTrace (twoSheetModel Y) (twoSheetDiagonal Y A B) =
      (normTrace Y A + normTrace Y B) / 2 := by
  classical
  have hcard : ((Fintype.card Y : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast hY.ne'
  simp only [normTrace]
  rw [card_twoSheetModel]
  simp only [Matrix.trace, Matrix.diag, twoSheetDiagonal,
    Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₂]
  push_cast
  field_simp [hcard]

/-- Every off-diagonal sheet-swap operator has normalized trace zero. -/
theorem normTrace_twoSheetDiagonal_mul_swap (Y : FiniteModel)
    (A B : Matrix Y Y ℂ) :
    normTrace (twoSheetModel Y)
      (twoSheetDiagonal Y A B * twoSheetSwap Y) = 0 := by
  classical
  unfold normTrace twoSheetDiagonal twoSheetSwap Matrix.trace
  rw [Matrix.fromBlocks_multiply, Fintype.sum_sum_type]
  simp

/-- Doubling averages squared Hilbert--Schmidt errors on the two sheets. -/
theorem hsDistSq_twoSheetDiagonal (Y : FiniteModel)
    (A B C D : Matrix Y Y ℂ) :
    hsDistSq (twoSheetModel Y) (twoSheetDiagonal Y A B)
        (twoSheetDiagonal Y C D) =
      (hsDistSq Y A C + hsDistSq Y B D) / 2 := by
  classical
  simp only [hsDistSq]
  rw [card_twoSheetModel]
  simp only [twoSheetDiagonal, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂]
  simp
  ring

end GroupApproximation
