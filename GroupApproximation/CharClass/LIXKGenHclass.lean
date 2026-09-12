import GroupApproximation.CharClass.LIXKGenThomTerm
import GroupApproximation.CharClass.LIXHclass
import GroupApproximation.Meta.AxiomGuard

/-!
# `hclass` at rank `n`: the Thom class restricts to the top Chern class

Lane `lix-oddside-n` (leaf (5) of the Step C half).

`CharClass/LIXHclass.lean`'s `lixHclass` proves, at rank two,

```text
jE (u) = π^* (γ_r),
```

the image of the Thom class of the mapping-torus bundle pair in the absolute cohomology of the
total space is the pullback of the top mod-2 Chern class.  Its three generic lemmas
(`pull_bridgeChartIncl_lhSum`, `chernMul_top_unit`, and the bridge `relToAbs_bridgeTotal`) are
stated for an abstract bundle, so the rank-`n` statement is the same proof over
`KGen.lixBundle n`, `KGen.lixThomClassTerm n`, `KGen.lixChern n dd` and
`KGen.lixChern_top_eq_gamma n` (`CharClass/LIXKGenThomTerm.lean`).

## Main declaration

* `KGen.lixHclass` — **`hclass` at rank `n`.**
-/

open CategoryTheory TopologicalSpace
open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

namespace KGen

noncomputable section

open ThomChernDeg LH

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-- **`hclass` at rank `n`.**  The image of the Thom class under `lixJE` is the pullback, along
the bundle projection, of the top Chern class `lixChern n dd … (lixRank n dd)`. -/
theorem lixHclass (n : ℕ) {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hcont : Continuous (mappingTorus (Gen.Vmat n) G circHoriz circHeight))
    (hproj : ∀ q, IsStarProjection (mappingTorus (Gen.Vmat n) G circHoriz circHeight q)) :
    (lixJE n hGc hGu (2 * lixRank n dd)).hom (lixThomClassTerm n hGc hGu)
      = (lixPiStar n hGc hGu (2 * lixRank n dd)).hom
          (lixChern n dd (mappingTorus (Gen.Vmat n) G circHoriz circHeight) hcont hproj
            (lixRank n dd)) := by
  have hR : 1 ≤ lixRank n dd := one_le_lixRank n dd
  set a := thomJmTotal (lixBundle n G hGc hGu) (lixLHplus n hGc hGu)
    (lixThomClassTerm n hGc hGu) with ha
  have hrhs : pull (cmap (Bundle.totalPi (lixBundle n G hGc hGu))) (2 * lixRank n dd)
        (lixChern n dd (mappingTorus (Gen.Vmat n) G circHoriz circHeight) hcont hproj
          (lixRank n dd))
      = (lixPiStar n hGc hGu (2 * lixRank n dd)).hom
          (lixChern n dd (mappingTorus (Gen.Vmat n) G circHoriz circHeight) hcont hproj
            (lixRank n dd)) :=
    pull_eq_absPull (lixPi n hGc hGu) (2 * lixRank n dd) _
  have hcoord :
      (relToAbs (ZMod 2) (TopCat.of (Bundle.Proj (lixBundle n G hGc hGu).plusOne))
          (Set.range (Bundle.projIncl (lixBundle n G hGc hGu))) (2 * lixRank n dd)).hom
          (bridgeTotal (lixBundle n G hGc hGu) (2 * lixRank n dd)
            (lixThomClassTerm n hGc hGu))
        = ∑ i : Fin (lixRank n dd + 1),
            lhTerm (projMapOf (lixBundle n G hGc hGu).plusOne)
              (tautEulerOf (lixBundle n G hGc hGu).plusOne) (2 * lixRank n dd) (i : ℕ)
              (a i) := by
    have h1 : (lhTopEquiv (lixLHplus n hGc hGu)).symm
        ((relToAbs (ZMod 2) (TopCat.of (Bundle.Proj (lixBundle n G hGc hGu).plusOne))
          (Set.range (Bundle.projIncl (lixBundle n G hGc hGu))) (2 * lixRank n dd)).hom
          (bridgeTotal (lixBundle n G hGc hGu) (2 * lixRank n dd)
            (lixThomClassTerm n hGc hGu)))
        = a := by rw [ha, thomJmTotal_apply, thomJm_apply]
    have h2 : (relToAbs (ZMod 2) (TopCat.of (Bundle.Proj (lixBundle n G hGc hGu).plusOne))
          (Set.range (Bundle.projIncl (lixBundle n G hGc hGu))) (2 * lixRank n dd)).hom
          (bridgeTotal (lixBundle n G hGc hGu) (2 * lixRank n dd)
            (lixThomClassTerm n hGc hGu))
        = (lhTopEquiv (lixLHplus n hGc hGu)) a := by
      rw [← h1, LinearEquiv.apply_symm_apply]
    rw [h2]
    rfl
  refine (relToAbs_bridgeTotal (lixBundle n G hGc hGu) (2 * lixRank n dd)
    (lixThomClassTerm n hGc hGu)).trans ?_
  rw [hcoord, pull_bridgeChartIncl_lhSum (lixBundle n G hGc hGu) (lixRank n dd) hR a,
    ← hrhs]
  refine congrArg (pull (cmap (Bundle.totalPi (lixBundle n G hGc hGu)))
    (2 * lixRank n dd)) ?_
  rw [ha, thomJmTotal_lixThomClassTerm n hGc hGu, ThomDeg.thomLift_castSucc,
    neg_eq_self_two, lixChern_top_eq_gamma n hGc hGu hcont hproj]
  exact chernMul_top_unit _ hR

end

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.lixHclass

end GroupApproximation.CharClass
