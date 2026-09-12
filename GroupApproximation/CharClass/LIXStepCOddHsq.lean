import GroupApproximation.CharClass.LIXHsq
import GroupApproximation.CharClass.LIXStepCOddThom
import GroupApproximation.Meta.AxiomGuard

/-!
# Step C's odd side with the compatibility square discharged

Lane `lix-hsq`.

`lix_topClass_ne_zero_of_thom` takes eleven arguments; this file supplies one of them,
`hsq`, from `LIXHsq.lixHsq`, and passes the rest through unchanged.

**Its only real content is that the statement matches.**  A lane can prove a theorem whose
statement drifted from the binder it was written for — this fleet has done it — and no probe
of the lane's own modules can see that, because the lane never mentions the consumer.  The
one thing that does see it is applying the theorem at the binder, which is what this file
does.  It is cheap to read and expensive to build (it drags in the whole Thom and
Leray–Hirsch closure), which is why it lives here and not inside `LIXHsq`.

## Main result

* `lix_topClass_ne_zero_of_hsq` — **Step C's odd side over the remaining eleven-minus-one.**
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-- **Step C's odd side, with `hsq` discharged.**  Every other argument of
`lix_topClass_ne_zero_of_thom` is passed through untouched. -/
theorem lix_topClass_ne_zero_of_hsq (hdd : ∀ j, 0 < dd j)
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
    (hres : Function.Injective (lixRes hGc hGu (2 * lixRank dd)).hom)
    {gamma : cohomologyZMod2 (lixN dd) (2 * lixRank dd)}
    (hclass : jE.hom (lixThomClassTerm hGc hGu) = piStar.hom gamma) :
    gamma ≠ 0 :=
  lix_topClass_ne_zero_of_thom hdd hGc hGu hGe j i hexact jE sAbs piStar hnat hsection
    (lixHsq hGc hGu hGe) hres hclass

/-! Audited on every build: `#audit_axioms` prints the closure **and fails the
build** if it leaves the classical allowlist, which `#print axioms` does not. -/

#audit_axioms lix_topClass_ne_zero_of_hsq

end GroupApproximation.CharClass
