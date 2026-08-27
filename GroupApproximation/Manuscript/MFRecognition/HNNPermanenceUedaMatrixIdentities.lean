import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaOperations

/-!
# Two-by-two identities used by Ueda's corner covariance
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {K : Type} [CStarAlgebra K]

theorem cStarDiagonalTwo_zero_eq_matrixUnit (b : K) :
    cStarDiagonalTwo 0 b = cStarMatrixUnitTwo 1 1 b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cStarDiagonalTwo, cStarMatrixUnitTwo]

theorem cStarDiagonalTwo_eq_matrixUnit_zero (b : K) :
    cStarDiagonalTwo b 0 = cStarMatrixUnitTwo 0 0 b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cStarDiagonalTwo, cStarMatrixUnitTwo]

theorem matrixUnit_ten_diagonal_zero_zeroOne (b : K) :
    cStarMatrixUnitTwo 1 0 1 * cStarDiagonalTwo b 0 *
        cStarMatrixUnitTwo 0 1 1 = cStarDiagonalTwo 0 b := by
  rw [cStarMatrixUnitTwo_mul_diagonal]
  simp
  rw [cStarMatrixUnitTwo_mul, cStarDiagonalTwo_zero_eq_matrixUnit]
  simp

theorem matrixUnit_zeroOne_zeroDiagonal_ten (b : K) :
    cStarMatrixUnitTwo 0 1 1 * cStarDiagonalTwo 0 b *
        cStarMatrixUnitTwo 1 0 1 = cStarDiagonalTwo b 0 := by
  rw [cStarMatrixUnitTwo_mul_diagonal]
  simp
  rw [cStarMatrixUnitTwo_mul, cStarDiagonalTwo_eq_matrixUnit_zero]
  simp

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
