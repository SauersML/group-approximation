import GroupApproximation.CharClass.ThomChartTautZero
import GroupApproximation.CharClass.ThomBridgeRelToAbs
import GroupApproximation.CharClass.ThomCoordinates
import GroupApproximation.CharClass.LIXChernTopGamma
import GroupApproximation.CharClass.LIXStepCOddRelative
import GroupApproximation.CharClass.CohomologyLHRestrict
import GroupApproximation.CharClass.MayerVietorisBiproduct

/-!
# `hclass`: the Thom class restricts to the top Chern class

Lane `lix-hclass` of the STW Problem LIX strike team (2026-09-07), on top of
`cc-thom`'s Thom-class stack.

`lix_topClass_ne_zero_of_thom` (`CharClass/LIXStepCOddThom.lean`) takes eleven
binders; this file discharges `hclass`, the one that carries the geometry:

```text
jE (u) = π^* (γ_r),
```

the image of the Thom class in the absolute cohomology of the total space is the
pullback of the top mod-2 Chern class.  With `jE` and `π^*` the concrete
`lixJE` and `lixPiStar` of `CharClass/LIXStepCOddRelative.lean`, this is provable;
`LIXChernTopGamma`'s docstring records that it is **not** provable while they are
free binders, and that is still true — nothing here weakens that statement, it
supplies the instantiation it asks for.

## The proof in one paragraph

The Thom class is named on the vector-bundle pair and its Leray--Hirsch
coordinates are read on the projectivisation pair, so the first step is
`ThomBridgeRelToAbs.relToAbs_bridgeTotal`: the two `relToAbs` differ by
restriction to the affine chart.  On the projectivisation, `relToAbs u` is by
construction the Leray--Hirsch combination `∑_i π^*(a_i) ⌣ ξ^i` of the class's
coordinates, and `ThomCoordinates.thomJmTotal_lixThomClassTerm` says those
coordinates are `thomLift` of the unit: the top one is `1` and the `i`-th is the
Chern coefficient `γ_{r-i}`.  Restricting to the chart kills `ξ`
(`ThomChartTautZero`), so every column but `i = 0` dies and the `i = 0` column is
`π^*(1 ⌣ γ_r) = π^*(γ_r)`.  Finally `LIXChernTopGamma.lixChern_top_eq_gamma`
identifies the endgame's `gamma` with `γ_r`.

## What this does not do

It does not discharge `hres` or `hsq`, and it proves nothing about the
**section**: the class compared here is the one the *projection* pulls back, not
the one the section detects.  The nonvanishing of `gamma` is still the consumer's
conclusion, from `hres` and this equation together, not from this equation alone.

## Main declarations

* `gamma_top_eq_chernCoeff`, `chernMul_top_unit` — the top Chern class is the
  zeroth reindexed coefficient, and multiplying the unit by it returns it.
* `pull_bridgeChartIncl_lhSum` — **restricting a Leray--Hirsch combination to the
  affine chart leaves the `i = 0` column.**
* `lixHclass` — **`hclass`.**
-/

open CategoryTheory TopologicalSpace
open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

open ThomChernDeg LH

set_option linter.unusedSectionVars false

/-! ## 1. The top Chern class as a coefficient -/

/-- Two Leray--Hirsch coefficients at indices with the same underlying natural
number agree, after the degree transport that the index sits inside. -/
theorem gammaCoeff_eq_of_val {X P : TopCat.{0}} {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) {k l : ℕ} (hk : k < lhDomainCard r (2 * r))
    (hl : l < lhDomainCard r (2 * r)) (h : k = l) :
    cohCast (show 2 * r - 2 * k = 2 * r - 2 * l by rw [h]) (L.gammaCoeff ⟨k, hk⟩)
      = L.gammaCoeff ⟨l, hl⟩ := by
  subst h
  exact cohCast_self _ _

/-- **The top mod-2 Chern class is the zeroth reindexed coefficient.**  `gammaOf`
reads it at index `r - r`, `chernCoeff` reads it at index `0`, and the two indices
have the same underlying natural number. -/
theorem gamma_top_eq_chernCoeff {X P : TopCat.{0}} {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) (hr : 1 ≤ r) :
    L.gamma r = chernCoeff L ⟨0, hr⟩ := by
  rw [L.gamma_eq_gammaOf hr (le_refl r)]
  exact gammaCoeff_eq_of_val L _ _ (Nat.sub_self r)

/-- **Multiplying the unit by the top Chern coefficient returns the top Chern
class.**  All that happens is three degree transports collapsing. -/
theorem chernMul_top_unit {X P : TopCat.{0}} {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) (hr : 1 ≤ r) :
    chernMul L ⟨0, hr⟩ (cohCast (show (0 : ℕ) = 2 * r - 2 * r by omega) (one X))
      = L.gamma r := by
  rw [chernMul_apply, cup_cohCast_left, one_cup', cohCast_cohCast, cohCast_cohCast,
    gamma_top_eq_chernCoeff L hr]
  exact cohCast_self _ _

/-! ## 2. Column terms at a vanishing class -/

/-- A column above the zeroth vanishes when the class does. -/
theorem lhTerm_zero_class {X P : TopCat.{0}} (π : P ⟶ X) (n i : ℕ) (hi : 0 < i)
    (a : Hmod2 X (n - 2 * i)) : lhTerm π (0 : Hmod2 P 2) n i a = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  by_cases h : 2 * (j + 1) ≤ n
  · rw [lhTerm_of_le π (0 : Hmod2 P 2) h]
    have h0 : cupPowE (0 : Hmod2 P 2) (j + 1) = 0 := by rw [cupPowE_succ, cup_zero]
    rw [h0, cup_zero, cohCast_zero]
  · rw [lhTerm_of_gt π (0 : Hmod2 P 2) h]

/-- The zeroth column is the pullback, whatever the class.  `LH.lhTerm_index_zero`
is the same statement at the degrees `n + 2`; this one is at an arbitrary degree,
which is what the sum collapse below needs, and it carries a different name for
that reason rather than shadowing theirs. -/
theorem lhTerm_at_index_zero {X P : TopCat.{0}} (π : P ⟶ X) (ξ : Hmod2 P 2) (n : ℕ)
    (a : Hmod2 X (n - 2 * 0)) : lhTerm π ξ n 0 a = pull π n a := by
  rw [lhTerm_of_le π ξ (show 2 * 0 ≤ n by omega), cupPowE_zero, cup_one]
  exact cohCast_self _ _

/-! ## 3. Restricting a Leray--Hirsch combination to the affine chart -/

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **A Leray--Hirsch combination restricted to the affine chart is its zeroth
column.**  `ξ` dies on the chart, so every higher cup power does, and the zeroth
column is the pullback along the bundle projection because the chart inclusion
lies over the base. -/
theorem pull_bridgeChartIncl_lhSum (p : Bundle X ι) (r : ℕ) (hr : 1 ≤ r)
    (a : (i : Fin (r + 1)) → Hmod2 (TopCat.of X) (2 * r - 2 * (i : ℕ))) :
    pull (cmap (bridgeChartIncl p)) (2 * r)
        (∑ i : Fin (r + 1), lhTerm (projMapOf p.plusOne) (tautEulerOf p.plusOne)
          (2 * r) (i : ℕ) (a i))
      = pull (cmap (Bundle.totalPi p)) (2 * r) (a ((⟨0, hr⟩ : Fin r).castSucc)) := by
  have hsum : pull (cmap (bridgeChartIncl p)) (2 * r)
      (∑ i : Fin (r + 1), lhTerm (projMapOf p.plusOne) (tautEulerOf p.plusOne)
        (2 * r) (i : ℕ) (a i))
      = ∑ i : Fin (r + 1), pull (cmap (bridgeChartIncl p)) (2 * r)
          (lhTerm (projMapOf p.plusOne) (tautEulerOf p.plusOne) (2 * r) (i : ℕ) (a i)) :=
    map_sum (pullLinear (cmap (bridgeChartIncl p)) (2 * r)) _ Finset.univ
  have hterm : ∀ i : Fin (r + 1),
      pull (cmap (bridgeChartIncl p)) (2 * r)
          (lhTerm (projMapOf p.plusOne) (tautEulerOf p.plusOne) (2 * r) (i : ℕ) (a i))
        = lhTerm (cmap (Bundle.totalPi p))
            (0 : Hmod2 (TopCat.of (Bundle.Total p)) 2) (2 * r) (i : ℕ) (a i) := fun i =>
    LHCast.pull_lhTerm (cmap (bridgeChartIncl p)) (projMapOf p.plusOne)
      (cmap (Bundle.totalPi p)) (bridgeChartIncl_comp_projMapOf p)
      (tautEulerOf p.plusOne) 0 (LH.pull_bridgeChartIncl_tautEulerOf p) (2 * r) (i : ℕ) (a i)
  rw [hsum]
  simp only [hterm]
  rw [Finset.sum_eq_single ((⟨0, hr⟩ : Fin r).castSucc)]
  · exact lhTerm_at_index_zero _ _ _ _
  · intro b _ hb
    refine lhTerm_zero_class _ _ _ ?_ _
    rcases Nat.eq_zero_or_pos (b : ℕ) with h0 | h0
    · exact absurd (Fin.val_injective h0) hb
    · exact h0
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## 4. `hclass` -/

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-- **`hclass`.**  The image of the Thom class under `lixJE` is the pullback,
along the bundle projection, of the endgame's top Chern class.

This is the `hclass` of `lix_topClass_ne_zero_of_thom` at `jE := lixJE`,
`piStar := lixPiStar`, `HE := lixHE` and `gamma := lixChern … (lixRank dd)`.  No
hypothesis is added beyond the two the bundle is built from and the two
`lixChern` takes; in particular `hdd` is not needed. -/
theorem lixHclass (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hcont : Continuous (mappingTorus Vmat G circHoriz circHeight))
    (hproj : ∀ q, IsStarProjection (mappingTorus Vmat G circHoriz circHeight q)) :
    (RelativeSupport.lixJE hGc hGu (2 * lixRank dd)).hom (lixThomClassTerm hGc hGu)
      = (RelativeSupport.lixPiStar hGc hGu (2 * lixRank dd)).hom
          (lixChern dd (mappingTorus Vmat G circHoriz circHeight) hcont hproj
            (lixRank dd)) := by
  have hR : 1 ≤ lixRank dd := one_le_lixRank_dd dd
  -- The Leray--Hirsch coordinate family of the Thom class, named once.  Writing
  -- `ThomDeg.thomLift …` inline instead makes `M` a metavariable at the point
  -- `lhTerm`'s argument is elaborated; that is the trap `LIXThomClassTerm`
  -- records, and naming the family avoids repeating its `(M := …)` pin.
  set a := thomJmTotal (lixBundle G hGc hGu) (lixLHplus hGc hGu)
    (lixThomClassTerm hGc hGu) with ha
  -- `lixPiStar` **is** the pullback along the bundle projection; named rather
  -- than left as a `rfl` calc step so that a failure here would be reported here.
  have hrhs : pull (cmap (Bundle.totalPi (lixBundle G hGc hGu))) (2 * lixRank dd)
        (lixChern dd (mappingTorus Vmat G circHoriz circHeight) hcont hproj
          (lixRank dd))
      = (RelativeSupport.lixPiStar hGc hGu (2 * lixRank dd)).hom
          (lixChern dd (mappingTorus Vmat G circHoriz circHeight) hcont hproj
            (lixRank dd)) :=
    pull_eq_absPull (RelativeSupport.lixPi hGc hGu) (2 * lixRank dd) _
  -- the coordinates, as a Leray--Hirsch combination upstairs
  have hcoord :
      (relToAbs (ZMod 2) (TopCat.of (Bundle.Proj (lixBundle G hGc hGu).plusOne))
          (Set.range (Bundle.projIncl (lixBundle G hGc hGu))) (2 * lixRank dd)).hom
          (bridgeTotal (lixBundle G hGc hGu) (2 * lixRank dd) (lixThomClassTerm hGc hGu))
        = ∑ i : Fin (lixRank dd + 1),
            lhTerm (projMapOf (lixBundle G hGc hGu).plusOne)
              (tautEulerOf (lixBundle G hGc hGu).plusOne) (2 * lixRank dd) (i : ℕ)
              (a i) := by
    have h1 : (lhTopEquiv (lixLHplus hGc hGu)).symm
        ((relToAbs (ZMod 2) (TopCat.of (Bundle.Proj (lixBundle G hGc hGu).plusOne))
          (Set.range (Bundle.projIncl (lixBundle G hGc hGu))) (2 * lixRank dd)).hom
          (bridgeTotal (lixBundle G hGc hGu) (2 * lixRank dd)
            (lixThomClassTerm hGc hGu)))
        = a := by rw [ha, thomJmTotal_apply, thomJm_apply]
    have h2 : (relToAbs (ZMod 2) (TopCat.of (Bundle.Proj (lixBundle G hGc hGu).plusOne))
          (Set.range (Bundle.projIncl (lixBundle G hGc hGu))) (2 * lixRank dd)).hom
          (bridgeTotal (lixBundle G hGc hGu) (2 * lixRank dd) (lixThomClassTerm hGc hGu))
        = (lhTopEquiv (lixLHplus hGc hGu)) a := by
      rw [← h1, LinearEquiv.apply_symm_apply]
    rw [h2]
    rfl
  -- `calc` is deliberately not used: the chain starts in `lixHE` and ends in
  -- `Hmod2 (TopCat.of (Bundle.Total …))`, two spellings of one object that
  -- `Trans` instance search cannot reconcile because `lixTotalPair` is a plain
  -- `def`.  `Eq.trans` unifies them, instance search does not.
  refine (relToAbs_bridgeTotal (lixBundle G hGc hGu) (2 * lixRank dd)
    (lixThomClassTerm hGc hGu)).trans ?_
  rw [hcoord, pull_bridgeChartIncl_lhSum (lixBundle G hGc hGu) (lixRank dd) hR a,
    ← hrhs]
  refine congrArg (pull (cmap (Bundle.totalPi (lixBundle G hGc hGu)))
    (2 * lixRank dd)) ?_
  rw [ha, thomJmTotal_lixThomClassTerm hGc hGu, ThomDeg.thomLift_castSucc,
    neg_eq_self_two, lixChern_top_eq_gamma hGc hGu hcont hproj]
  exact chernMul_top_unit _ hR

/-! Printed on every build. -/

#print axioms lixHclass

end

end GroupApproximation.CharClass
