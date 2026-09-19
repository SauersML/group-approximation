import GroupApproximation.Leavitt.LeavittSimplicity

/-!
# Strong division in the binary Leavitt algebra

Simplicity supplies the strong-division lemma used by the window-reduction
argument.  The completed diagonal-class and `GL = EL` results are proved in
`KOne.RefineLoopDischarge`.
-/

namespace GroupApproximation
namespace BinaryLeavitt

variable (k : Type) [Field k]

/-- Strong division for the binary Leavitt algebra, from simplicity. -/
theorem division :
    ∀ x : BinaryLeavittAlgebra k, x ≠ 0 →
      ∃ p q : BinaryLeavittAlgebra k, p * x * q = 1 :=
  fun _ hx ↦ exists_mul_mul_eq_one k hx

end BinaryLeavitt
end GroupApproximation
