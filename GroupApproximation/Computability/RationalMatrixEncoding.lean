import GroupApproximation.Analysis.RatComplexSubfield
import GroupApproximation.Computability.EffectiveMatrixCode

/-!
# Encoding rational complex matrices by executable matrix codes

`RatComplexSubfield.exists_rat_unitary_close` produces an exactly unitary
matrix whose entries have rational real and imaginary parts.  This file closes
the semantic gap between that statement and `EffectiveMatrixCode`: every such
entry has a `ComplexCode`, hence every matrix on the natural nonempty basis
`Fin (d + 1)` has a row-major `MatrixCode` representing it exactly.

Consequently every unitary matrix on `Fin (d + 1)` is arbitrarily close to the
interpretation of an exactly-unitary `MatrixCode`.
-/

namespace GroupApproximation
namespace RationalMatrixEncoding

open scoped Matrix
open scoped Matrix.Norms.L2Operator

open RatComplexSubfield RationalComplexCode EffectiveMatrixCode

noncomputable section

/-- Every complex number with rational real and imaginary parts has an
executable Gaussian-rational code. -/
theorem exists_complexCode_of_isRat {z : ℂ} (hz : IsRat z) :
    ∃ q : ComplexCode, toComplex q = z := by
  obtain ⟨p, hp⟩ := exists_ofRatPair_of_isRat hz
  obtain ⟨q, hq⟩ := exists_toComplex_of_ratPair p
  exact ⟨q, hq.trans hp.symm⟩

/-- A rational-entry matrix on the natural nonempty basis is represented
exactly by a row-major executable matrix code. -/
theorem exists_matrixCode_of_isRat (d : ℕ)
    (A : Matrix (Fin (dim d)) (Fin (dim d)) ℂ)
    (hA : ∀ i j, IsRat (A i j)) :
    ∃ C : MatrixCode, toMatrix d C = A := by
  classical
  have hentry : ∀ i j : Fin (dim d), ∃ q : ComplexCode, toComplex q = A i j :=
    fun i j ↦ exists_complexCode_of_isRat (hA i j)
  choose q hq using hentry
  refine ⟨List.ofFn fun i : Fin (dim d) =>
      List.ofFn fun j : Fin (dim d) => q i j, ?_⟩
  ext i j
  simpa [toMatrix] using hq i j

/-- Every unitary matrix in a natural nonempty dimension is arbitrarily close
to the interpretation of an exactly-unitary executable matrix code. -/
theorem exists_unitary_matrixCode_close (d : ℕ)
    {U : Matrix (Fin (dim d)) (Fin (dim d)) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin (dim d)) ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : MatrixCode,
      isUnitary d C ∧ ‖U - toMatrix d C‖ < ε := by
  obtain ⟨Q, hQunitary, hQclose⟩ := exists_rat_unitary_close hU hε
  obtain ⟨C, hC⟩ := exists_matrixCode_of_isRat d
    (RationalHermitian.ofRat Q) (fun i j ↦ isRat_ofRatPair (Q i j))
  refine ⟨C, (isUnitary_iff d C).2 ?_, ?_⟩
  · rwa [hC]
  · rwa [hC]

end

end RationalMatrixEncoding
end GroupApproximation
