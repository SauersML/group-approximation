import GroupApproximation.CharClass.LerayHirschColumnPack
import GroupApproximation.CharClass.LerayHirschBridge

/-!
# The ladder at general rank

Leray–Hirsch at general rank, over the one statement still owed.  The spanning half
is unconditional; the freeness half is `HasFreeTuple`, the free-module statement for
a product with a projective factor, which `cc-cohom-api` is building.

There is nothing between that statement and the graded interface but the
repackaging, so this file is short by design: it exists to name the endpoint and to
fix, in one place, exactly which hypothesis the whole ladder rests on.

## Main declarations

* `lerayHirschGraded_of_freeTuple` — **the ladder**, over `HasFreeTuple`.
* `lerayHirschGraded_cpProd_of_freeTuple` — the same at `U × ℂP^d`.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory
open GroupApproximation.STW59

noncomputable section

variable {X P : TopCat.{0}}

/-- **Leray–Hirsch at general rank**, over the free-module statement. -/
theorem lerayHirschGraded_of_freeTuple (π : P ⟶ X) (ξ : Hmod2 P 2) (r : ℕ)
    (h : HasFreeTuple π ξ r) : LerayHirschGraded π ξ r :=
  lerayHirschGraded_of_bijective π ξ r (fun n => bijective_lhSum_of_freeTuple π ξ r h n)

/-- The same for a product with a projective factor, at the rank the fibre forces. -/
theorem lerayHirschGraded_cpProd_of_freeTuple (U : Type) [TopologicalSpace U]
    (d : ℕ) (hd : 1 ≤ d)
    (h : HasFreeTuple (KnCP.cpFst U d) (pull (KnCP.cpSnd U d) 2 (cpGen d hd)) (d + 1)) :
    LerayHirschGraded (KnCP.cpFst U d) (pull (KnCP.cpSnd U d) 2 (cpGen d hd)) (d + 1) :=
  lerayHirschGraded_of_freeTuple _ _ _ h

end

end LH
end CharClass
end GroupApproximation
