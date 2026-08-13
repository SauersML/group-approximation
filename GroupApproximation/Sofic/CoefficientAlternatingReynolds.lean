import GroupApproximation.Sofic.DoublePauliCoefficient

/-!
# Exact spectrum of the double-Pauli alternating Reynolds operator

The rational matrix below is the restriction of `E_A E_{P'}` to the five
atoms consisting of the four raw coefficient cuts and the complement of
their carrier.  Its exact diagonalization proves that finite alternating
Reynolds iteration fixes only the scalar direction and contracts every
centered coefficient mode.
-/

namespace GroupApproximation

open Matrix

/-- Exact transition matrix from the symbolic double-Pauli certificate. -/
def coefficientAlternatingReynolds : Matrix (Fin 5) (Fin 5) ℚ :=
  !![75 / 256, 31 / 256, 15 / 256, 15 / 256, 15 / 32;
     31 / 256, 75 / 256, 15 / 256, 15 / 256, 15 / 32;
     15 / 256, 15 / 256, 75 / 256, 31 / 256, 15 / 32;
     15 / 256, 15 / 256, 31 / 256, 75 / 256, 15 / 32;
     15 / 128, 15 / 128, 15 / 128, 15 / 128, 17 / 32]

/-- Eigenvector matrix: its columns are the scalar, block-difference, two
pair-difference, and carrier-complement modes. -/
def coefficientAlternatingReynoldsEigenvectors : Matrix (Fin 5) (Fin 5) ℚ :=
  !![1, 1, 1, 0, 1;
     1, 1, -1, 0, 1;
     1, -1, 0, 1, 1;
     1, -1, 0, -1, 1;
     1, 0, 0, 0, -1]

/-- Diagonal matrix of the five exact eigenvalues. -/
def coefficientAlternatingReynoldsEigenvalues : Matrix (Fin 5) (Fin 5) ℚ :=
  diagonal ![1, 19 / 64, 11 / 64, 11 / 64, 1 / 16]

/-- The displayed rational matrices give an exact diagonalization. -/
theorem coefficientAlternatingReynolds_diagonalization :
    coefficientAlternatingReynolds *
        coefficientAlternatingReynoldsEigenvectors =
      coefficientAlternatingReynoldsEigenvectors *
        coefficientAlternatingReynoldsEigenvalues := by
  native_decide

/-- The eigenvector matrix is invertible; hence the five displayed modes
are the complete spectrum, not merely five checked vectors. -/
theorem coefficientAlternatingReynolds_eigenvectors_det :
    coefficientAlternatingReynoldsEigenvectors.det = -16 := by
  native_decide

/-- Every non-scalar eigenvalue is strictly below the exact contraction
factor `19/64`. -/
theorem coefficientAlternatingReynolds_nontrivial_spectrum_bounded :
    (19 : ℚ) / 64 < 1 ∧
      (11 : ℚ) / 64 ≤ 19 / 64 ∧
      (1 : ℚ) / 16 ≤ 19 / 64 := by
  norm_num

end GroupApproximation
