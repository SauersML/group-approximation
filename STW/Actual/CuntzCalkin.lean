import STW.Actual.FockPair
import GroupApproximation.Analysis.CStarQuotientHom

/-!
# The Cuntz generators in the Calkin algebra

The two Fock prefix shifts are genuine orthogonal isometries in `B(FockSpace)`.
Their images in the Calkin quotient therefore satisfy the first three Cuntz
relations exactly.  The remaining range-sum relation is the statement that the
vacuum defect is compact, proved below in this development rather than assumed.
-/

namespace STW.Actual

noncomputable section

open GroupApproximation

abbrev FockCalkin := CalkinAlgebra.CalkinQuotient FockSpace

/-- The quotient map `B(FockSpace) → Q(FockSpace)` as a star-algebra hom. -/
noncomputable def essentialStar :
    (FockSpace →L[ℂ] FockSpace) →⋆ₐ[ℂ] FockCalkin :=
  CStarTensor.quotientStarMk (CalkinAlgebra.compactIdeal FockSpace)

@[simp] theorem essentialStar_apply (T : FockSpace →L[ℂ] FockSpace) :
    essentialStar T = CalkinAlgebra.essential FockSpace T := rfl

/-- The two prospective Cuntz generators in the Calkin algebra. -/
def calkinPrefix (b : Bool) : FockCalkin := essentialStar (prefixOp b)

/-- Each Calkin prefix generator is an isometry. -/
theorem calkinPrefix_star_mul_self (b : Bool) :
    star (calkinPrefix b) * calkinPrefix b = 1 := by
  rw [← map_star (essentialStar) (prefixOp b), ← map_mul]
  rw [prefixOp_star_mul_self]
  exact map_one essentialStar

/-- Distinct Calkin prefix generators have orthogonal ranges. -/
theorem calkinPrefix_star_mul_of_ne {b c : Bool} (hbc : b ≠ c) :
    star (calkinPrefix b) * calkinPrefix c = 0 := by
  rw [← map_star (essentialStar) (prefixOp b), ← map_mul]
  rw [prefixOp_star_mul_of_ne hbc]
  exact map_zero essentialStar

@[simp] theorem calkinPrefix_star_mul_false_true :
    star (calkinPrefix false) * calkinPrefix true = 0 :=
  calkinPrefix_star_mul_of_ne (by decide)

@[simp] theorem calkinPrefix_star_mul_true_false :
    star (calkinPrefix true) * calkinPrefix false = 0 :=
  calkinPrefix_star_mul_of_ne (by decide)

end

end STW.Actual
