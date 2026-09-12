import GroupApproximation.CharClass.LerayHirschProduct
import GroupApproximation.CharClass.LerayHirschCover
import GroupApproximation.CharClass.LerayHirschTransport

/-!
# The chart step, assembled

Over an open set on which a rank-two bundle is trivial, the situation is a product
with `ℂP^1`, and rank-two Leray–Hirsch over an arbitrary base is now
unconditional.  What remains is to move it across the trivialisation, which is
`bijective_lhSum_of_iso`.

`LHOver_two_of_prodIso` is that move, and it says exactly what a trivialisation has
to supply: an isomorphism of bases, an isomorphism of total spaces, a square that
commutes as spaces, and the identification of the classes.  Nothing about bundles
appears, so the geometry can be handed over independently of the cohomology.

Note what is *not* required: the base need not be contractible.  That matters,
because the induction over a cover produces intersections of trivialising sets with
arbitrary opens, and those are trivialising but not contractible.

## Main declarations

* `LHOver_two_of_prodIso` — **the chart step**, over the trivialisation.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace

noncomputable section

variable {X P : TopCat.{0}}

/-- **Leray–Hirsch over a trivialising open, at rank two.**  The trivialisation
enters only as an isomorphism of situations carrying one class to the other. -/
theorem LHOver_two_of_prodIso (f : P ⟶ X) (ξ : Hmod2 P 2) (U : Opens X)
    (V : Type) [TopologicalSpace V]
    (eX : opSpace U ≅ TopCat.of V)
    (eP : opSpace (opensComap f U) ≅ KnCP.cpProdTop V 0)
    (hsq : eP.hom ≫ KnCP.cpPrU V 0 = opensRestrict f U ≫ eX.hom)
    (hξ : pull eP.hom 2 (KnCP.cpTaut V) = lhClass f ξ U) :
    LHOver f ξ 2 U :=
  fun n =>
    bijective_lhSum_of_iso (opensRestrict f U) (KnCP.cpPrU V 0) eX eP hsq
      (lhClass f ξ U) (KnCP.cpTaut V) hξ 2 n (bijective_lhSum_cpProd V n)

end

end LH
end CharClass
end GroupApproximation
