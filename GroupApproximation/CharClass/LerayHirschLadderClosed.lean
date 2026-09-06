import GroupApproximation.CharClass.LerayHirschColSum
import GroupApproximation.CharClass.LerayHirschLadder

/-!
# Leray–Hirsch at general rank, unconditionally

Both clauses of `HasFreeTuple` are now proved, so the hypothesis the ladder rested
on discharges and Leray–Hirsch holds at every rank over an arbitrary base, with no
compactness and no hypothesis of any kind.

What made it work, in one line each.  The spanning half is a downward induction on
the degree, peeling with `cc-cohom-api`'s Künneth and stopping at their floor.  The
freeness half is their tower freeness, read through a reflection.  Both meet the
column through the same two vanishings, above the tower's length and above the rank,
and the ring of `ℂP^r` enters exactly once, to kill the powers above the rank.

## Main declarations

* `hasFreeTuple_cpProd` — **the free-module statement**, unconditionally.
* `lerayHirschGraded_cpProd_general` — **Leray–Hirsch at general rank**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

/-- **The free-module statement, unconditionally.**  Both clauses, at every degree
and every rank, over an arbitrary base. -/
theorem hasFreeTuple_cpProd (U : Type) [TopologicalSpace U] (d : ℕ) (hd : 1 ≤ d + 1) :
    HasFreeTuple (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 (cpGen (d + 1) hd)) (d + 2) :=
  fun n =>
    ⟨fun z => exists_freeTuple U d hd n z,
      fun a hside hzero => freeTuple_unique U d hd n a hside hzero⟩

/-- **Leray–Hirsch at general rank, unconditionally.**  `H^*(U × ℂP^r)` is free over
`H^*(U)` on the powers of the pulled-back generator, at every degree, every rank and
any base. -/
theorem lerayHirschGraded_cpProd_general (U : Type) [TopologicalSpace U] (d : ℕ)
    (hd : 1 ≤ d + 1) :
    LerayHirschGraded (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 (cpGen (d + 1) hd))
      (d + 2) :=
  lerayHirschGraded_of_freeTuple _ _ _ (hasFreeTuple_cpProd U d hd)

end

end LH
end CharClass
end GroupApproximation
