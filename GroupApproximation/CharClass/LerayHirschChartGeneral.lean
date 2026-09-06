import GroupApproximation.CharClass.LerayHirschColumnPack
import GroupApproximation.CharClass.LerayHirschChartTwo

/-!
# The chart step at general rank

`LHOver_two_of_prodIso` transports Leray–Hirsch across an isomorphism of situations
when the fibre is `ℂP^1`.  This is the same statement at an arbitrary fibre, and it
is the same proof: the transport lemma never cared about the rank, only the rank-two
product instance did.

So the chart step at general rank is exactly the general-rank product instance,
which is the ladder, which rests on `HasFreeTuple`.  Every consumer that needs
Leray–Hirsch for a projectivised bundle of rank above two — the mapping torus, the
flag bundle, the slice class — goes through here.

## Main declarations

* `LHOver_of_prodIso` — **the chart step**, at any rank, over `HasFreeTuple`.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace
open GroupApproximation.STW59

noncomputable section

variable {X P : TopCat.{0}}

/-- **The chart step at general rank.**  Over an open set of the base whose part of
the total space is a product with `ℂP^d`, compatibly with the projections and with
the class, Leray–Hirsch holds at rank `d + 1`.

The rank-two case is `LHOver_two_of_prodIso`; the only difference is which product
instance is fed in, and at general rank that is the ladder. -/
theorem LHOver_of_prodIso (f : P ⟶ X) (ξ : Hmod2 P 2) (U : Opens X) (d : ℕ) (hd : 1 ≤ d)
    (V : Type) [TopologicalSpace V]
    (hfree : HasFreeTuple (KnCP.cpFst V d) (pull (KnCP.cpSnd V d) 2 (cpGen d hd)) (d + 1))
    (eX : opSpace U ≅ TopCat.of V)
    (eP : opSpace (opensComap f U) ≅ TopCat.of (V × CP d))
    (hsq : eP.hom ≫ KnCP.cpFst V d = opensRestrict f U ≫ eX.hom)
    (hξ : pull eP.hom 2 (pull (KnCP.cpSnd V d) 2 (cpGen d hd)) = lhClass f ξ U) :
    LHOver f ξ (d + 1) U :=
  fun n =>
    bijective_lhSum_of_iso (opensRestrict f U) (KnCP.cpFst V d) eX eP hsq
      (lhClass f ξ U) (pull (KnCP.cpSnd V d) 2 (cpGen d hd)) hξ (d + 1) n
      (bijective_lhSum_of_freeTuple _ _ _ hfree n)

end

end LH
end CharClass
end GroupApproximation
