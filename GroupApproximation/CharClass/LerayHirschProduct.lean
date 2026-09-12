import GroupApproximation.CharClass.LerayHirschRankTwo
import GroupApproximation.CharClass.CohomologyChartRankTwoInterface

/-!
# Rank-two Leray–Hirsch for a trivial `ℂP^1`-bundle

`cc-cohom-api`'s four statements about the chart cover of a product with `ℂP^1`
are exactly the hypotheses of `bijective_lhSum_two`, and in the tautological basis
rather than a comparable substitute, so the instance is an application.

That is the base case of the whole bootstrap: rank-two Leray–Hirsch over an
*arbitrary* base, with no ring structure used anywhere.  The triangular change of
basis in `LerayHirschShift` turned out not to be needed, because their connecting
class is the pulled-back generator on the nose; it is kept for the higher ranks,
where the two do differ.

## Main declarations

* `bijective_lhSum_cpProd` — **rank-two Leray–Hirsch for `U × ℂP^1 → U`**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

/-- **Rank-two Leray–Hirsch for the trivial `ℂP^1`-bundle over an arbitrary base.**
The powers `1, ξ` of the tautological class are a basis of the cohomology of the
product over that of the base, in every degree. -/
theorem bijective_lhSum_cpProd (U : Type) [TopologicalSpace U] (n : ℕ) :
    Function.Bijective (lhSum (KnCP.cpPrU U 0) (KnCP.cpTaut U) 2 n) :=
  bijective_lhSum_two (KnCP.cpPrU U 0) (KnCP.cpTaut U)
    (KnCP.lhLow U) (KnCP.lhSurj U) (KnCP.lhUniq U) n

/-- The same, as the published graded interface. -/
theorem lerayHirschGraded_cpProd (U : Type) [TopologicalSpace U] :
    LerayHirschGraded (KnCP.cpPrU U 0) (KnCP.cpTaut U) 2 :=
  lerayHirschGraded_of_bijective (KnCP.cpPrU U 0) (KnCP.cpTaut U) 2
    (bijective_lhSum_cpProd U)

end

end LH
end CharClass
end GroupApproximation
