import GroupApproximation.CharClass.LerayHirschChartBundleGen
import GroupApproximation.CharClass.ChernEulerIndex

/-!
# The class identification at general rank

`LerayHirschChartClass` identifies the tautological class of `P(p ⊕ 1)` over a chart
with the pulled-back generator of `ℂP¹`.  This is the same statement at an arbitrary
rank, and the same three steps: restricting the class restricts the bundle by
naturality, pushing the index forward commutes with pulling back, and the Euler class
does not see the index it is computed at.

The geometric input is the same as at rank two and is `cc-bundle`'s: over the chart
the tautological line of the projectivised bundle *is* the pullback of the
tautological line of `ℂP^r`.  At rank two that was `tautLineIsoCPOne`.  Here it is a
hypothesis, stated as a `BundleIso`, because the rank-`r` analogue does not exist yet
and belongs to their lane.

Nothing else is assumed.  In particular no generator computation appears: the index
change is absorbed by `eulerOfBundle_pushforward_eq_of_bundleIso`, exactly as at rank
two.

## Main declarations

* `tautEmbOf`, `tautEulerOf` — **the class `ξ`** for a bundle of any rank.
* `pull_chartProdIsoOf_cpGen` — **the identification**, over the bundle isomorphism.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.CPn

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A `Fin` large enough to hold the index and to descend from. -/
abbrev tautCardOf (ι : Type) [Fintype ι] : ℕ := Fintype.card ι

/-- An injection of the bundle's index into that `Fin`. -/
def tautEmbOf (ι : Type) [Fintype ι] : ι → Fin (1 + tautCardOf ι + 1) :=
  fun s => Fin.castLE (Nat.le_succ_of_le (Nat.le_add_left _ 1)) (Fintype.equivFin ι s)

theorem tautEmbOf_injective (ι : Type) [Fintype ι] : Function.Injective (tautEmbOf ι) :=
  (Fin.castLE_injective _).comp (Fintype.equivFin ι).injective

/-- **The class `ξ`** for a projectivised bundle of any rank: the Euler class of its
tautological line, taken at an index large enough to compare with `ℂP^r`. -/
def tautEulerOf (p : Bundle X ι) : Hmod2 (TopCat.of (Proj p)) 2 :=
  eulerOfBundle (show 1 ≤ 1 + tautCardOf ι by omega)
    (pushforward (tautEmbOf ι) (tautEmbOf_injective ι) (tautLine p))
    (trace_pushforward_one (tautEmbOf ι) (tautEmbOf_injective ι) (tautLine p)
      (trace_tautLine p))

/-- The workhorse with the common index size given by an equation rather than
definitionally.  `subst` reduces it to the definitional form; without it the index
arithmetic is a truncated subtraction over a variable and the application is an
`isDefEq` timeout rather than a type error. -/
theorem eulerOfBundle_pushforward_eq_of_bundleIso' (a k N : ℕ) (hN : a + k = N)
    (ha : 1 ≤ a) (p : Bundle X ι) (q : Bundle X (Fin (a + 1))) (e : BundleIso p q)
    (hq : ∀ x, (q x).trace = 1) {f : ι → Fin (N + 1)} (hf : Function.Injective f)
    (hfp : ∀ x, (pushforward f hf p x).trace = 1) :
    eulerOfBundle (show 1 ≤ N by omega) (pushforward f hf p) hfp
      = eulerOfBundle ha q hq := by
  subst hN
  exact eulerOfBundle_pushforward_eq_of_bundleIso a k ha p q e hq hf hfp

/-- **The class identification at general rank.**  Under the chart trivialisation the
tautological class is the restriction of `tautEulerOf p`, given that the tautological
line is the pullback of the one on `ℂP^r`. -/
theorem pull_chartProdIsoOf_cpGen (p : Bundle X ι) (U : Opens (TopCat.of X)) (r : ℕ)
    (hr : 1 ≤ r)
    (e : BundleIso (p.restrictTo ((U : Opens (TopCat.of X)) : Set X))
      (triv ↥((U : Opens (TopCat.of X)) : Set X) (Fin (r + 1))))
    (chartCP : C(↥(opSpace (opensComap (projMapOf p) U)), CP r))
    (hchart : cmap chartCP
      = (chartProdIsoOf p U r e).hom ≫ KnCP.cpSnd _ r)
    (chartIncl : C(↥(opSpace (opensComap (projMapOf p) U)), Proj p))
    (hincl : LH.opIncl (opensComap (projMapOf p) U) = cmap chartIncl)
    (hrc : r ≤ tautCardOf ι)
    (etaut : BundleIso (comap chartIncl (tautLine p)) (comap chartCP (cpTaut r))) :
    pull (chartProdIsoOf p U r e).hom 2
        (pull (KnCP.cpSnd ↥((U : Opens (TopCat.of X)) : Set X) r) 2 (cpGen r hr))
      = lhClass (projMapOf p) (tautEulerOf p) U := by
  have hL : pull (chartProdIsoOf p U r e).hom 2
        (pull (KnCP.cpSnd ↥((U : Opens (TopCat.of X)) : Set X) r) 2 (cpGen r hr))
      = eulerOfBundle hr (comap chartCP (cpTaut r))
          (fun w => trace_cpTaut r (chartCP w)) := by
    rw [eulerOfBundle_comap, ← eulerOfBundle_cpTaut r hr, hchart, pull_comp]
  have hR : lhClass (projMapOf p) (tautEulerOf p) U
      = eulerOfBundle (show 1 ≤ 1 + tautCardOf ι by omega)
          (pushforward (tautEmbOf ι) (tautEmbOf_injective ι)
            (comap chartIncl (tautLine p)))
          (fun w => trace_pushforward_one (tautEmbOf ι) (tautEmbOf_injective ι)
            (tautLine p) (trace_tautLine p) (chartIncl w)) := by
    rw [lhClass, hincl, tautEulerOf, ← eulerOfBundle_comap]
    rfl
  rw [hL, hR]
  exact (eulerOfBundle_pushforward_eq_of_bundleIso' r (1 + tautCardOf ι - r)
    (1 + tautCardOf ι) (by omega) hr
    (comap chartIncl (tautLine p)) (comap chartCP (cpTaut r)) etaut
    (fun w => trace_cpTaut r (chartCP w)) (tautEmbOf_injective ι) _).symm

end

end LH
end CharClass
end GroupApproximation
