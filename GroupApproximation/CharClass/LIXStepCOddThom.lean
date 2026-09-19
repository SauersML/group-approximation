import GroupApproximation.CharClass.LIXStepCOddLocal
import GroupApproximation.CharClass.LIXRestrictionMap
import GroupApproximation.CharClass.LIXThomClassTerm

/-!
# Step C's odd side with the Thom class and the restriction supplied

Lane `cc-lix-odd`.

Two more of `lix_topClass_ne_zero_of_local`'s arguments are now terms rather than
hypotheses:

* `u` and `hu` are `cc-thom`'s `lixThomClassTerm` and its nonvanishing, landed
  **unconditionally** once `cc-projective` discharged the tautological restriction;
* `res` is this lane's `lixRes`, the pullback along `cc-bundle`'s inclusion.

`u` had to be a named term rather than an existential, and the reason is worth keeping:
the class appears in **two** hypotheses of one theorem, `hu` and `hclass`, which must be
about the same term.  An existential does not merely fail to help there, it removes the
ability to state the second at all.

## What is left

`j`, `i`, `hexact` for the base pair and `jE`, `sAbs`, `piStar`, `hnat`, `hsection` for the
bundle pair, all `cc-relative`'s; and `hsq`, `hres`, `hclass`, all `cc-thom`'s.

`hres` is **not** available from excision: `cc-bundle`'s own note explains that excision
needs a set whose closure lies inside the punctured set, and any such set contains
zero-section points, which the punctured set omits.

## Main result

* `lix_topClass_ne_zero_of_thom` — **Step C's odd side over the remaining eight.**
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-- **Step C's odd side**, with the Thom class, its nonvanishing and the restriction map
all supplied. -/
theorem lix_topClass_ne_zero_of_thom (hdd : ∀ j, 0 < dd j)
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0)
    {HE : ModuleCat.{0} (ZMod 2)}
    (j : relCohomology (ZMod 2) (lixN dd)
          ({lixZero dd}ᶜ : Set (↥sphereOne × baseM dd)) (2 * lixRank dd) ⟶
        cohomologyZMod2 (lixN dd) (2 * lixRank dd))
    (i : cohomologyZMod2 (lixN dd) (2 * lixRank dd) ⟶
        cohomologyZMod2 (TopCat.of ↥({lixZero dd}ᶜ : Set (↥sphereOne × baseM dd)))
          (2 * lixRank dd))
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom)
    (jE : relCohomology (ZMod 2) (lixTotalPair hGc hGu) (lixPuncturedInTotal hGc hGu)
        (2 * lixRank dd) ⟶ HE)
    (sAbs : HE ⟶ cohomologyZMod2 (lixN dd) (2 * lixRank dd))
    (piStar : cohomologyZMod2 (lixN dd) (2 * lixRank dd) ⟶ HE)
    (hnat : lixSRel hGc hGu hGe (2 * lixRank dd) ≫ j = jE ≫ sAbs)
    (hsection : piStar ≫ sAbs = 𝟙 (cohomologyZMod2 (lixN dd) (2 * lixRank dd)))
    (hsq : lixSRel hGc hGu hGe (2 * lixRank dd)
        ≫ (lixRelModelIso dd (2 * lixRank dd)).hom
      = lixRes hGc hGu (2 * lixRank dd) ≫ (lixLocalPairIsoClosed hGc hGu).hom)
    (hres : Function.Injective (lixRes hGc hGu (2 * lixRank dd)).hom)
    {gamma : cohomologyZMod2 (lixN dd) (2 * lixRank dd)}
    (hclass : jE.hom (lixThomClassTerm hGc hGu) = piStar.hom gamma) :
    gamma ≠ 0 :=
  lix_topClass_ne_zero_of_local hdd hGc hGu hGe j i hexact jE sAbs piStar hnat hsection
    (lixRes hGc hGu (2 * lixRank dd)) hsq hres
    (lixThomClassTerm_ne_zero hGc hGu) hclass

end GroupApproximation.CharClass
