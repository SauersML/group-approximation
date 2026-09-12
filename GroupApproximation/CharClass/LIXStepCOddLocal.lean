import GroupApproximation.CharClass.LIXStepCOddNamed
import GroupApproximation.CharClass.LIXLocalPairClosed
import GroupApproximation.CharClass.ThomStepCOddLocal

/-!
# Step C's odd side over the local form

Lane `cc-lix-odd`.

`cc-thom` weakened the model bridge: where the isomorphism form asked for
`e : HrelE ≅ W` and an equation, the local form asks for a restriction `res` with only its
**injectivity**, an identification `loc` of the restricted pair with the local model, and a
square relating the two routes.

**`loc` is already this lane's and already unconditional.**  It is
`lixLocalPairIsoClosed`, the bundle pair over the contractible neighbourhood identified
with the local model, which `cc-relative`'s corollary closed earlier.  So the weakening
turns one open argument into one that was already discharged plus two smaller ones.

`cc-thom`'s reason for preferring this shape is the one this lane raised against their
earlier interface: with `t` an isomorphism, injectivity of the composite collapses to
injectivity of `sRel` alone and the chart buys nothing.  Here `res` and `t` are maps out of
different objects, so the square is a real constraint.

## What this supplies and what is left

Supplied here, all unconditional: `hacyclic`, `absLine`, `exc`, `chartIso`, `t`, `sRel`,
and now **`loc`**.  Still named: the pair's exact sequence, the bundle side's sequence and
splitting, `res` with `hres` and `hsq`, and the Thom class with `hclass`.

## Main result

* `lix_topClass_ne_zero_of_local` — **Step C's odd side over the local form.**
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-- **Step C's odd side, over `cc-thom`'s local form**, with this lane's seven objects
supplied including the identification of the restricted pair with the local model. -/
theorem lix_topClass_ne_zero_of_local (hdd : ∀ j, 0 < dd j)
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
    (res : relCohomology (ZMod 2) (lixTotalPair hGc hGu) (lixPuncturedInTotal hGc hGu)
        (2 * lixRank dd) ⟶
      relCohomology (ZMod 2)
        (TopCat.of (Bundle.Total
          ((lixBundle G hGc hGu).restrictTo (lixTrivBall hGc hGu))))
        {w : Bundle.Total ((lixBundle G hGc hGu).restrictTo (lixTrivBall hGc hGu)) |
          (w : ↥(lixTrivBall hGc hGu) × (VIdx dd ⊕ VIdx dd → ℂ))
            ∈ Bundle.puncturedSet
              ((lixBundle G hGc hGu).restrictTo (lixTrivBall hGc hGu))}
        (2 * lixRank dd))
    (hsq : lixSRel hGc hGu hGe (2 * lixRank dd)
        ≫ (lixRelModelIso dd (2 * lixRank dd)).hom
      = res ≫ (lixLocalPairIsoClosed hGc hGu).hom)
    (hres : Function.Injective res.hom)
    {u : relCohomology (ZMod 2) (lixTotalPair hGc hGu) (lixPuncturedInTotal hGc hGu)
      (2 * lixRank dd)}
    (hu : u ≠ 0)
    {gamma : cohomologyZMod2 (lixN dd) (2 * lixRank dd)}
    (hclass : jE.hom u = piStar.hom gamma) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_odd_local
    (puncturedAcyclic_lixZero' hbase_lix hdd)
    j i hexact (nonempty_absEquiv_lix dd hdd)
    (lixRelModelIso dd (2 * lixRank dd)) (Iso.refl _)
    jE (lixSRel hGc hGu hGe (2 * lixRank dd)) sAbs piStar hnat hsection
    (lixRelModelIso dd (2 * lixRank dd)).hom res (lixLocalPairIsoClosed hGc hGu)
    hsq hres hu hclass

end GroupApproximation.CharClass
