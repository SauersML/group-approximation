import GroupApproximation.CharClass.LerayHirschShiftTerm

/-!
# The tower's terms, in column coordinates

`cc-cohom-api`'s free-module statement is a Horner tower whose coefficients are
indexed so that their degree *grows* with the index and the generator's power
shrinks.  `lhTerm` indexes them the other way round: degree shrinking, power
growing.  Same content, opposite order, related by `i ↦ k - i`.

Neither convention is free.  Theirs is forced by cast-freeness — degrees written as
`m + 2 * j` with the power on the right are the only arrangement in which the
successor step is definitional — and `lhTerm`'s is forced by `lhDomain` being
published.  So a reindex has to exist, and it belongs on this side, where the
repackaging lives; that keeps truncated subtraction out of the producer's file
entirely.

This is the reindex, one term at a time, and it is stated against the shape of a
tower summand rather than against the tower, so it does not wait on their
definition.

## Main declarations

* `lhTerm_of_tower` — **a tower summand is a column term** at the reflected index.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

variable {X P : TopCat.{0}}

/-- **A tower summand is a column term at the reflected index.**  The coefficient of
`ξ^(k-i)` in degree `m + 2k` carries degree `m + 2i`, which is what the column
records at index `k - i`. -/
theorem lhTerm_of_tower (π : P ⟶ X) (ξ : Hmod2 P 2) (m k i : ℕ) (hi : i ≤ k)
    (a : Hmod2 X (m + 2 * i)) :
    lhTerm π ξ (m + 2 * k) (k - i)
        (cohCast (by omega : m + 2 * i = m + 2 * k - 2 * (k - i)) a)
      = cohCast (by omega : m + 2 * i + 2 * (k - i) = m + 2 * k)
          (cup (pull π (m + 2 * i) a) (cupPowE ξ (k - i))) := by
  rw [lhTerm_of_le π ξ (by omega : 2 * (k - i) ≤ m + 2 * k), pull_cohCast,
    cup_cohCast_left, cohCast_cohCast]

end

end LH
end CharClass
end GroupApproximation
