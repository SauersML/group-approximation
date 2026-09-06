import GroupApproximation.CharClass.LerayHirschSquares
import GroupApproximation.CharClass.ProjectiveSpaceRing
import GroupApproximation.CharClass.CohomologyAssoc
import GroupApproximation.CharClass.SteenrodCupOne

/-!
# Cupping with the class shifts a column term up one index

The general-rank Leray–Hirsch ladder is a downward induction on the degree: peel one
power of the generator off with the projective-factor Künneth, recurse, and put the
peel back.  Putting it back is this lemma, and it is the only place where the cup
product's associativity and commutativity are used at all.

The degrees are the point.  A term at index `i` in degree `m` carries a coefficient
of degree `m - 2i`, and at index `i+1` in degree `m+2` it carries `m + 2 - 2(i+1)`,
which is the same number on the nose.  So the coefficient crosses unchanged and no
transport is needed on it — only on the ambient degree, where `2 + m` and `m + 2`
differ as terms.

## Main declarations

* `lhTerm_succ` — **cupping with `ξ` raises the index by one**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

variable {X P : TopCat.{0}}

/-- **Cupping with the class raises the power by one.**

Stated with the degrees written as sums rather than through `lhTerm`, whose
coefficient degree is a truncated subtraction.  Handing `lhTerm` a degree of the
form `m + 2 - 2 * (i + 1)` and asking Lean to see it as `m - 2 * i` is a `whnf`
loop, not a cheap unification, so the shift is proved here in the form where every
degree is a sum and converted at the point of use. -/
theorem cup_cupPowE_succ (π : P ⟶ X) (ξ : Hmod2 P 2) (k i : ℕ) (a : Hmod2 X k) :
    cohCast (by omega : 2 + (k + 2 * i) = k + 2 * (i + 1))
        (cup ξ (cup (pull π k a) (cupPowE ξ i)))
      = cup (pull π k a) (cupPowE ξ (i + 1)) := by
  rw [cup_comm ξ, cohCast_cohCast, cupPowE_succ, ← cup_assoc]

end

end LH
end CharClass
end GroupApproximation
