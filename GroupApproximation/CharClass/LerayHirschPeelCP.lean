import GroupApproximation.CharClass.LerayHirschPeel
import GroupApproximation.CharClass.CohomologyChartKunnethClosed

/-!
# The peeling hypothesis, discharged

`cc-cohom-api`'s `cpSplit_closed` is `HasPeel` for the projection of a product with
a projective factor, on the nose: same projections, same generator, same order of
the two summands.  So the spanning half of the ladder runs over one hypothesis
rather than two, and the remaining one is the floor.

That the instantiation is an application with no cast is the point.  The shape was
agreed before either side built it, which is the only reason two lanes' notions of
"peel one power off" coincide definitionally.

## Main declarations

* `hasPeel_cpProd` — **the peeling hypothesis holds** for `U × ℂP^d`.
* `exists_col_cpProd` — every class on `U × ℂP^d` is a column, over the floor alone.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory
open GroupApproximation.STW59

noncomputable section

/-- **The peeling hypothesis holds**, from `cc-cohom-api`'s unconditional Künneth. -/
theorem hasPeel_cpProd (U : Type) [TopologicalSpace U] (d : ℕ) (hd : 1 ≤ d) :
    HasPeel (KnCP.cpFst U d) (pull (KnCP.cpSnd U d) 2 (cpGen d hd)) :=
  fun m z => KnCP.cpSplit_closed d hd U hd m z

/-- **Every class on `U × ℂP^d` is a column**, over the floor alone. -/
theorem exists_col_cpProd (U : Type) [TopologicalSpace U] (d : ℕ) (hd : 1 ≤ d)
    (hlow : HasLowSurj (KnCP.cpFst U d)) (n : ℕ)
    (z : Hmod2 (TopCat.of (U × CP d)) n) :
    ∃ c : (i : ℕ) → Hmod2 (TopCat.of U) (n - 2 * i),
      z = ∑ i ∈ Finset.range (n + 1),
        lhTerm (KnCP.cpFst U d) (pull (KnCP.cpSnd U d) 2 (cpGen d hd)) n i (c i) :=
  exists_col _ _ hlow (hasPeel_cpProd U d hd) n z

end

end LH
end CharClass
end GroupApproximation
