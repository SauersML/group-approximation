import GroupApproximation.Leavitt.AryWords
import Mathlib.Tactic.NoncommRing
import GroupApproximation.Meta.AxiomGuard

/-!
# Every monomial is a balanced one times a shift

`cor:leavitt-mf-quotient` needs `L_k(1,d)` presented as a corner skew Laurent
ring over its degree-zero part,

    `L = ∑ₙ L₀ t₊ⁿ + ∑ₙ t₋ⁿ L₀`,

and the spanning half of that presentation looks as if it needs the `ℤ`-grading.
It does not.  It is one cancellation on monomials, and this module is that
cancellation.

For any word `w`,

* `monomial_eq_balanced_mul_shift` --- `s_α t_β = (s_α t_{w·β}) · s_w`;
* `monomial_eq_shift_mul_balanced` --- `s_α t_β = t_w · (s_{w·α} t_β)`.

Both are `wordT w * wordS w = 1` (`CompleteMatrixFamily.wordT_mul_wordS_self`)
inserted and reassociated.  Choosing `w` of length `|α| − |β|` in the first, or
`|β| − |α|` in the second, makes the bracketed factor **balanced**, hence an
element of the degree-zero tower of `KOne/LeavittDegreeZeroTower.lean`.
`length_bracket_left` and `length_bracket_right` do that bookkeeping.

## The convention trap

`AryWords` defines `wordT (i :: a) = wordT a * F.right i`, so concatenation on
the `T` side **reverses**:

    `wordT (a ++ b) = wordT b * wordT a`   while   `wordS (a ++ b) = wordS a * wordS b`.

So the balanced factor above is `t_{w·β}` with `w` on the **left** of `β` — the
opposite side from where the analogous `s_{w·α}` puts it.  Writing `t_{β·w}`
gives a false statement.  This is the one place the two word conventions pull
in different directions.

## Scope

Only the spanning half.  The *directness* of the sum — that the degree-zero
component of an element is unique — is a different statement and needs the
independence of `Leavitt/AryLeavittBasis.lean` at the balanced layer together
with the shift.  Nothing here mentions the Leavitt algebra: it is about an
arbitrary complete matrix family.
-/

namespace GroupApproximation
namespace CompleteMatrixFamily

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)

/-- **A monomial is a balanced monomial times a positive shift.**  Padding the
`T`-word on the left by `w` and multiplying by `s_w` on the right is the
identity, because `t_w s_w = 1`. -/
theorem monomial_eq_balanced_mul_shift (w α β : List ι) :
    F.wordS α * F.wordT β
      = (F.wordS α * F.wordT (w ++ β)) * F.wordS w := by
  rw [F.wordT_append]
  rw [show F.wordS α * (F.wordT β * F.wordT w) * F.wordS w
      = F.wordS α * F.wordT β * (F.wordT w * F.wordS w) from by noncomm_ring,
    F.wordT_mul_wordS_self, mul_one]

/-- **A monomial is a negative shift times a balanced monomial.**  The mirror
statement: pad the `S`-word on the left by `w` and multiply by `t_w` on the
left. -/
theorem monomial_eq_shift_mul_balanced (w α β : List ι) :
    F.wordS α * F.wordT β
      = F.wordT w * (F.wordS (w ++ α) * F.wordT β) := by
  rw [F.wordS_append]
  rw [show F.wordT w * (F.wordS w * F.wordS α * F.wordT β)
      = (F.wordT w * F.wordS w) * (F.wordS α * F.wordT β) from by noncomm_ring,
    F.wordT_mul_wordS_self, one_mul]

/-- The bracketed factor of `monomial_eq_balanced_mul_shift` is balanced exactly
when `w` takes up the length defect. -/
theorem length_bracket_left (w α β : List ι)
    (h : w.length + β.length = α.length) :
    (w ++ β).length = α.length := by
  rw [List.length_append]
  exact h

/-- The bracketed factor of `monomial_eq_shift_mul_balanced` is balanced exactly
when `w` takes up the length defect. -/
theorem length_bracket_right (w α β : List ι)
    (h : w.length + α.length = β.length) :
    (w ++ α).length = β.length := by
  rw [List.length_append]
  exact h

end CompleteMatrixFamily
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.monomial_eq_balanced_mul_shift
#audit_axioms GroupApproximation.CompleteMatrixFamily.monomial_eq_shift_mul_balanced
#audit_axioms GroupApproximation.CompleteMatrixFamily.length_bracket_left
#audit_axioms GroupApproximation.CompleteMatrixFamily.length_bracket_right
