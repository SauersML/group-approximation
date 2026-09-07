import GroupApproximation.CharClass.LIXStepCOddThom
import GroupApproximation.CharClass.LIXStepCOddRelative

/-!
# Step C's odd side, wired to the eight relative terms

Lane `cs-endpoint` of the STW Problem LIX program.

`cc-lix-odd`'s `lix_topClass_ne_zero_of_thom` (`LIXStepCOddThom.lean`) takes eleven
arguments beyond the given data `hdd`, `hGc`, `hGu`, `hGe`: `j`, `i`, `hexact`, `jE`,
`sAbs`, `piStar`, `hnat`, `hsection`, `hsq`, `hres`, `hclass`.  `cc-relative`'s
`LIXStepCOddRelative.lean` supplies terms for the first eight of those --- `lixJ`,
`lixI`, `lixHexact`, `lixJE`, `lixSAbs`, `lixPiStar`, `lixHnat`, `lixHsection` --- so
plugging them in leaves exactly three: `hsq`, `hres`, `hclass`.  Those three are the
targets of lanes `lix-hsq`, `lix-hres` and `lix-hclass`.

The one trap is the implicit `HE`: `LIXStepCOddRelative` names it `lixHE`, an
`abbrev`, and `lix_topClass_ne_zero_of_thom` takes it as an implicit argument, so it
is pinned by name rather than left to unification.

## Main result

* `lix_topClass_ne_zero_of_three` --- **Step C's odd side, over three hypotheses.**
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-- **Step C's odd side, collapsed to the three open hypotheses.**  The eight
relative-cohomology terms of `RelativeSupport` are plugged into
`lix_topClass_ne_zero_of_thom` in place, leaving only `hsq` (the model/restriction
square), `hres` (injectivity of the restriction) and `hclass` (the Thom class pulls
back to `gamma`). -/
theorem lix_topClass_ne_zero_of_three (hdd : ∀ j, 0 < dd j)
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0)
    (hsq : lixSRel hGc hGu hGe (2 * lixRank dd)
        ≫ (lixRelModelIso dd (2 * lixRank dd)).hom
      = lixRes hGc hGu (2 * lixRank dd) ≫ (lixLocalPairIsoClosed hGc hGu).hom)
    (hres : Function.Injective (lixRes hGc hGu (2 * lixRank dd)).hom)
    {gamma : cohomologyZMod2 (lixN dd) (2 * lixRank dd)}
    (hclass : (RelativeSupport.lixJE hGc hGu (2 * lixRank dd)).hom
        (lixThomClassTerm hGc hGu)
      = (RelativeSupport.lixPiStar hGc hGu (2 * lixRank dd)).hom gamma) :
    gamma ≠ 0 :=
  lix_topClass_ne_zero_of_thom hdd hGc hGu hGe
    (HE := RelativeSupport.lixHE hGc hGu (2 * lixRank dd))
    (RelativeSupport.lixJ dd (2 * lixRank dd))
    (RelativeSupport.lixI dd (2 * lixRank dd))
    (RelativeSupport.lixHexact dd (2 * lixRank dd))
    (RelativeSupport.lixJE hGc hGu (2 * lixRank dd))
    (RelativeSupport.lixSAbs hGc hGu hGe (2 * lixRank dd))
    (RelativeSupport.lixPiStar hGc hGu (2 * lixRank dd))
    (RelativeSupport.lixHnat hGc hGu hGe (2 * lixRank dd))
    (RelativeSupport.lixHsection hGc hGu hGe (2 * lixRank dd))
    hsq hres hclass

end GroupApproximation.CharClass
