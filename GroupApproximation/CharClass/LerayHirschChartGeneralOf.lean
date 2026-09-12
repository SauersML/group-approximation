import GroupApproximation.CharClass.LerayHirschChartGeneral

/-!
# The chart step at general rank, over a coefficient ring

The coefficient-generic twin of `LerayHirschChartGeneral.LHOver_of_prodIso`.  The transport
(`bijective_lhSum_of_iso`) and the column shape (`bijective_lhSum_of_freeTuple`) are already
generic in the coefficients.  The only `F₂` datum in the `F₂` statement is the fibre class
`cpGen d hd`, and here it is an arbitrary class `hfib ∈ H^2(ℂP^d; K)`: which class it is gets
decided by the free-module statement the caller supplies.

## Main declarations

* `LH.LHOver_of_prodIsoOf` — **the chart step**, at any rank and over any commutative ring.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace
open GroupApproximation.STW59

noncomputable section

variable {X P : TopCat.{0}}

/-- **The chart step at general rank, over `K`.**  Over an open set of the base whose part of
the total space is a product with `ℂP^d`, compatibly with the projections and with the class,
Leray–Hirsch holds at rank `d + 1`, given the free-module statement for the product with the
fibre class `hfib`. -/
theorem LHOver_of_prodIsoOf (K : Type) [CommRing K] (f : P ⟶ X) (ξ : Hmod K P 2)
    (U : Opens X) (d : ℕ) (V : Type) [TopologicalSpace V] (hfib : Hmod K (CPtop d) 2)
    (hfree : HasFreeTuple (KnCP.cpFst V d) (pull (KnCP.cpSnd V d) 2 hfib) (d + 1))
    (eX : opSpace U ≅ TopCat.of V)
    (eP : opSpace (opensComap f U) ≅ TopCat.of (V × CP d))
    (hsq : eP.hom ≫ KnCP.cpFst V d = opensRestrict f U ≫ eX.hom)
    (hξ : pull eP.hom 2 (pull (KnCP.cpSnd V d) 2 hfib) = lhClass f ξ U) :
    LHOver f ξ (d + 1) U :=
  fun n =>
    bijective_lhSum_of_iso (opensRestrict f U) (KnCP.cpFst V d) eX eP hsq
      (lhClass f ξ U) (pull (KnCP.cpSnd V d) 2 hfib) hξ (d + 1) n
      (bijective_lhSum_of_freeTuple _ _ _ hfree n)

end

end LH
end CharClass
end GroupApproximation
