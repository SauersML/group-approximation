import GroupApproximation.CharClass.LerayHirschPeelCP
import GroupApproximation.CharClass.CohomologyChartLowDegree

/-!
# The ladder's spanning half, unconditionally

`cc-cohom-api`'s `lhLow_general` is the floor hypothesis on the nose, so the last
input to the spanning half discharges and it holds outright: every class on
`U × ℂP^d` is a column, at every degree and every rank, over any base.

Both inputs came from the same lane and neither needed a cast.  Worth noting what
they are, because they are not the same kind of statement.  `cpSplit_closed` is the
Künneth, and it is what does the work.  `lhLow_general` is fibre connectivity, and
it is only the floor the induction stops at; it is invisible to the Künneth, which
is why it had to be asked for separately.

This is the spanning half only.  Freeness does *not* follow by iterating a one-step
uniqueness: a coefficient living on the total space is pinned only modulo the kernel
of cupping with the generator, and that kernel is nonzero once the degree reaches
twice the rank.  The freeness half consumes the full iterated decomposition instead.

## Main declarations

* `hasLowSurj_cpProd` — the floor, discharged.
* `exists_col_cpProd_closed` — **every class is a column**, unconditionally.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory
open GroupApproximation.STW59

noncomputable section

/-- **The floor, discharged** against `cc-cohom-api`'s `lhLow_general`. -/
theorem hasLowSurj_cpProd (U : Type) [TopologicalSpace U] (d : ℕ) :
    HasLowSurj (KnCP.cpFst U d) :=
  fun n hn => (KnCP.lhLow_general U d n hn).2

/-- **Every class on `U × ℂP^d` is a column**, unconditionally: the spanning half of
Leray–Hirsch at general rank, over any base. -/
theorem exists_col_cpProd_closed (U : Type) [TopologicalSpace U] (d : ℕ) (hd : 1 ≤ d)
    (n : ℕ) (z : Hmod2 (TopCat.of (U × CP d)) n) :
    ∃ c : (i : ℕ) → Hmod2 (TopCat.of U) (n - 2 * i),
      z = ∑ i ∈ Finset.range (n + 1),
        lhTerm (KnCP.cpFst U d) (pull (KnCP.cpSnd U d) 2 (cpGen d hd)) n i (c i) :=
  exists_col_cpProd U d hd (hasLowSurj_cpProd U d) n z

end

end LH
end CharClass
end GroupApproximation
