import GroupApproximation.CharClass.LIXChartIso
import GroupApproximation.CharClass.LIXBundlePair
import GroupApproximation.CharClass.LemmaTwoStepCAbsEquiv
import GroupApproximation.CharClass.ThomStepCOddIso

/-!
# Step C's odd side, with everything this lane holds supplied

Lane `cc-lix-odd`.

`topChernClass_ne_zero_odd_iso` takes sixteen arguments.  Six of them are objects this lane
now owns outright, and this file supplies them, leaving the rest named so that each
incoming landing discharges one hypothesis by one application.

**Supplied here, all unconditional:**

* `hacyclic` — the punctured acyclicity at the section's zero;
* `absLine` — the top line of the base, as a `Nonempty`;
* `exc` — `LIXChartIso`'s identification of the pair's relative group with the local model;
* `chartIso` — the identity, because `exc` already lands in the local model;
* `t` — the same identification, read as a morphism;
* `sRel` — the section pullback of `LIXBundlePair`.

**Still named**, each in the shape its owner publishes:

* `j`, `i`, `hexact` — the pair's exact sequence (`cc-relative`, requested as a
  range-equals-kernel equality);
* `jE`, `sAbs`, `piStar`, `hnat`, `hsection` — the bundle side's sequence and the
  projection splitting;
* `e`, `hcomp` — the model bridge (`cc-thom`'s step three).  **`hcomp` carries the whole
  content**: since `t` is an isomorphism, injectivity of the composite is never weaker than
  injectivity of `sRel` alone, so nothing is discharged by the choice of `t`;
* `u`, `hu`, `hclass` — the Thom class (`cc-thom`'s `LIXThomDatum`).

## Main result

* `lix_topClass_ne_zero_of_named` — **Step C's odd side at the real objects.**
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-- **Step C's odd side, with this lane's six objects supplied.**

Every remaining argument is named in the shape its owner publishes, so each landing closes
one of them by a single application and nothing else here moves. -/
theorem lix_topClass_ne_zero_of_named (hdd : ∀ j, 0 < dd j)
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
    (e : relCohomology (ZMod 2) (lixTotalPair hGc hGu) (lixPuncturedInTotal hGc hGu)
          (2 * lixRank dd)
        ≅ relCohomology (ZMod 2) (TopCat.of (Fin (lixRank dd) → ℂ))
          (puncturedSet (lixRank dd)) (2 * lixRank dd))
    (hcomp : lixSRel hGc hGu hGe (2 * lixRank dd)
        ≫ (lixRelModelIso dd (2 * lixRank dd)).hom = e.hom)
    {u : relCohomology (ZMod 2) (lixTotalPair hGc hGu) (lixPuncturedInTotal hGc hGu)
      (2 * lixRank dd)}
    (hu : u ≠ 0)
    {gamma : cohomologyZMod2 (lixN dd) (2 * lixRank dd)}
    (hclass : jE.hom u = piStar.hom gamma) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_odd_iso
    (puncturedAcyclic_lixZero' hbase_lix hdd)
    j i hexact (nonempty_absEquiv_lix dd hdd)
    (lixRelModelIso dd (2 * lixRank dd)) (Iso.refl _)
    jE (lixSRel hGc hGu hGe (2 * lixRank dd)) sAbs piStar hnat hsection
    (lixRelModelIso dd (2 * lixRank dd)).hom e hcomp hu hclass

end GroupApproximation.CharClass
