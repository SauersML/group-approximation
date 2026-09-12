import Mathlib.Algebra.GroupWithZero.Defs

/-!
# A zero-range obstruction for algebraic partial isometries

If `a * b` is an idempotent while the reverse product `b * a` vanishes, then
that idempotent vanishes.  This is the purely multiplicative endpoint used by
the eventual-zero germ quotient of the hard Leavitt-atlas packet; positivity,
a trace, and characteristic zero are not required.
-/

namespace GroupApproximation

variable {R : Type*} [SemigroupWithZero R]

theorem idempotent_eq_zero_of_factors_reverse_zero
    {a b e : R} (hab : a * b = e) (hba : b * a = 0)
    (he : e * e = e) :
    e = 0 := by
  calc
    e = e * e := he.symm
    _ = (a * b) * (a * b) := by rw [hab]
    _ = a * (b * a) * b := by simp only [mul_assoc]
    _ = 0 := by rw [hba]; simp

theorem no_factors_with_reverse_zero_of_nonzero_idempotent
    {e : R} (he : e * e = e) (hne : e ≠ 0) :
    ¬ ∃ a b : R, a * b = e ∧ b * a = 0 := by
  rintro ⟨a, b, hab, hba⟩
  exact hne (idempotent_eq_zero_of_factors_reverse_zero hab hba he)

end GroupApproximation
