import GroupApproximation.CharClass.ThomHyperplaneLH
import GroupApproximation.CharClass.LIXBaseInstances
import GroupApproximation.CharClass.LIXBundleModel
import GroupApproximation.CharClass.LIXThomDatum

/-!
# The Thom class at `cc-lix-odd`'s objects, over one named input

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`lix_topClass_ne_zero_of_named` takes a class `u` of the relative group of the
mapping-torus bundle pair together with `hu : u ≠ 0`.  This file produces both, at
the mapping-torus bundle, over the single input `htaut` of
`ThomChernDeg.thomData_total_of_taut`.

Everything else is landed: the rank is `rank_lixBundle` and its `plusOne`
companion, the base instances are `LIXBaseInstances`, the Leray--Hirsch instances
are `cc-projective`'s compact-base theorem and its transport to the hyperplane,
the pair algebra is `ThomDataFromLH`, and the bridge to the vector-bundle pair is
`ThomBridgeTotal`.

The generator is the unit class of the base in degree zero, which is nonzero
because the base is nonempty; `one_ne_zero_cohZero` is the whole argument.

## Main declarations

* `ThomChernDeg.lixTopCoeff` — the generator of the top coefficient group.
* `exists_lixThomClass_ne_zero` — **`u` and `hu`**, over `htaut`.
-/

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace ThomChernDeg

open LH

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-! ## 1. The generator of the top coefficient group -/

/-- A degree transport of a nonzero class is nonzero. -/
theorem cohCast_ne_zero {Z : TopCat.{0}} {m m' : ℕ} (h : m = m') {a : Hmod2 Z m}
    (ha : a ≠ 0) : cohCast h a ≠ 0 := by
  subst h; exact ha

/-- The generator of the top Leray–Hirsch coefficient group, which is `H^0` of the
base. -/
def lixTopCoeff (dd : Fin ℓ → ℕ) :
    Hmod2 (lixN dd) (2 * lixRank dd - 2 * lixRank dd) :=
  cohCast (by omega) (one (lixN dd))

/-- **The generator is nonzero**, because the base is nonempty. -/
theorem lixTopCoeff_ne_zero (dd : Fin ℓ → ℕ) : lixTopCoeff dd ≠ 0 := by
  haveI : Nonempty ↥(lixN dd) := inferInstanceAs (Nonempty (↥sphereOne × baseM dd))
  exact cohCast_ne_zero _ (one_ne_zero_cohZero (lixN dd))

/-! ## 2. The Thom class -/

/-- **The Thom class of the mapping-torus bundle pair, and its nonvanishing.**

This is the `u` and the `hu` of `lix_topClass_ne_zero_of_named`, over the single
input `htaut`: that the tautological class of `P(W_g ⊕ 1)` restricts to the
tautological class of `P(W_g)`. -/
theorem exists_lixThomClass_ne_zero (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (htaut : pull (sInclusion (Set.range (Bundle.projIncl (lixBundle G hGc hGu)) :
          Set ↥(TopCat.of (Bundle.Proj (lixBundle G hGc hGu).plusOne)))) 2
        (tautEulerOf (lixBundle G hGc hGu).plusOne)
      = pull (hyperIso (lixBundle G hGc hGu)).hom 2
        (tautEulerOf (lixBundle G hGc hGu))) :
    ∃ u : ↥(relCohomology (ZMod 2) (lixTotalPair hGc hGu)
      (lixPuncturedInTotal hGc hGu) (2 * lixRank dd)), u ≠ 0 := by
  have hr : 1 ≤ lixRank dd := by simp [lixRank]
  obtain ⟨jm, hinj, hrange⟩ :=
    thomData_total_of_taut (lixBundle G hGc hGu) (lixRank dd)
      (rank_lixBundle G hGc hGu) hr (rank_lixBundle_plusOne G hGc hGu) htaut
  exact ⟨lixThomClass hGc hGu (2 * lixRank dd) (lixRank dd) _ jm hinj hrange
      (lixTopCoeff dd),
    lixThomClass_ne_zero hGc hGu (2 * lixRank dd) (lixRank dd) _ jm hinj hrange
      (lixTopCoeff_ne_zero dd)⟩

/-! Printed on every build. -/

#print axioms exists_lixThomClass_ne_zero

end ThomChernDeg

end

end GroupApproximation.CharClass
