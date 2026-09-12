import GroupApproximation.CharClass.LIXKGenOfFibre
import GroupApproximation.CharClass.LIXKGenOfLocalSquare
import GroupApproximation.CharClass.LIXKGenChern
import GroupApproximation.CharClass.ThomJmNaturalOf
import GroupApproximation.CharClass.CohomologyTotalNontrivialOf
import GroupApproximation.CharClass.LerayHirschSquares
import GroupApproximation.CharClass.LerayHirschChartBundleGen
import GroupApproximation.Meta.AxiomGuard

/-!
# A class with unit top coordinate is nonzero over each zero, over a field

Lane `lx-stepcK-local` (LIX strongest swarm, 2026-09-12): the fibre input `hfib` of
`KGen.kGenLocalNonzeroOf_of_fibre`, for any class whose Thom coordinates have the unit of `H^0` on
top, such as the Thom class over `K` (`lixThomClassTermOf`, lane `lx-stepcK-agree`).

The route is `CharClass/LIXResFibre.lean`'s at `F₂`, over a field.  Restricting the bundle pair to a
subset `U` of a compact Hausdorff base restricts the Thom coordinates coordinatewise
(`ThomChernDeg.thomJmTotal_restrictOf`).  If the restricted class were zero, every restricted
coordinate would vanish, the top one included; but the top coordinate is the unit, and the unit
restricts to the unit, which is nonzero over a nonempty space.  At `U = {z_i}` that is
`LIXKGenOfFibre`'s input.

The Leray–Hirsch statements upstairs (`L`, over the base) and over the singleton (`L'`) are
arguments, with their generators' compatibility `hξ`: they are what the compact Leray–Hirsch
theorem over `K` supplies, and no argument below depends on which generators are used.

## Main declarations

* `KGen.cohCast_ne_zeroOf`, `KGen.pull_cohCast_one_ne_zeroOf` — the unit survives restriction.
* `KGen.totalInclOn_relPullback_ne_zero_of_top` — **the class survives restriction to `U`.**
* `KGen.lixKFibre_ne_zero_of_top` — the fibre class at each zero is nonzero.
* `KGen.kGenLocalNonzeroOf_of_top` — **`KGenLocalNonzeroOf K n k … u` for a class with unit top
  coordinate.**
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.CharClass.LH
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

/-! ## 1. The unit survives restriction -/

/-- A degree transport of a nonzero class is nonzero, over any ring. -/
theorem cohCast_ne_zeroOf {K : Type} [CommRing K] {Z : TopCat.{0}} {m m' : ℕ} (h : m = m')
    {a : Hmod K Z m} (ha : a ≠ 0) : cohCast h a ≠ 0 := by
  subst h
  exact ha

/-- **The unit, transported to any degree index equal to zero, restricts to a nonzero class over
a nonempty space**, over a field. -/
theorem pull_cohCast_one_ne_zeroOf (K : Type) [Field K] {X Y : TopCat.{0}} [Nonempty Y]
    (f : Y ⟶ X) {m : ℕ} (h : 0 = m) :
    pull f m (cohCast h (one (K := K) X)) ≠ 0 := by
  rw [LH.pull_cohCast, pull_one]
  exact cohCast_ne_zeroOf h (one_ne_zero_cohZeroOf K Y)

/-! ## 2. Restriction to a subset of the base -/

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **A class of the bundle pair whose restricted top coordinate is nonzero survives the
restriction to `U`**, over a field. -/
theorem totalInclOn_relPullback_ne_zero_of_top (K : Type) [Field K] [CompactSpace X] [T2Space X]
    (p : Bundle X ι) (U : Set X) [CompactSpace ↥U] [T2Space ↥U] {r : ℕ}
    {ξ : Hmod K (TopCat.of (Bundle.Proj p.plusOne)) 2}
    {ξ' : Hmod K (TopCat.of (Bundle.Proj (p.restrictTo U).plusOne)) 2}
    (hξ : pull (cmap (Bundle.projInclOn p.plusOne U)) 2 ξ = ξ')
    (L : LerayHirschGraded (projMapOf p.plusOne) ξ (r + 1))
    (L' : LerayHirschGraded (projMapOf ((p.restrictTo U).plusOne)) ξ' (r + 1))
    (x : ↥(relCohomology K (TopCat.of (Bundle.Total p))
      ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) (2 * r)))
    (htop : pull (inclSubtype U) (2 * r - 2 * ((Fin.last r : Fin (r + 1)) : ℕ))
      (ThomChernDeg.thomJmTotalOf K p L x (Fin.last r)) ≠ 0) :
    (relPullback K (cmap (Bundle.totalInclOn p U)) (totalInclOn_mapsTo p U) (2 * r)).hom x ≠ 0 := by
  intro h0
  have hcoord := ThomChernDeg.thomJmTotal_restrictOf K p U hξ L L' x
  have hfin := congrFun hcoord (Fin.last r)
  simp only [h0, map_zero, Pi.zero_apply] at hfin
  exact htop hfin.symm

/-! ## 3. At the zeros of the `k`-section -/

variable {ℓ : ℕ}

/-- **The fibre class at the `i`-th zero is nonzero** for a class whose top Thom coordinate is the
unit. -/
theorem lixKFibre_ne_zero_of_top (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ)
    (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    {ξ : Hmod K (TopCat.of (Bundle.Proj (lixBundle n G hGc hGu).plusOne)) 2}
    {ξ' : Hmod K (TopCat.of
      (Bundle.Proj ((lixBundle n G hGc hGu).restrictTo (lixKPtSet n k dd i)).plusOne)) 2}
    (hξ : pull (cmap (Bundle.projInclOn (lixBundle n G hGc hGu).plusOne (lixKPtSet n k dd i))) 2
      ξ = ξ')
    (L : LerayHirschGraded (projMapOf (lixBundle n G hGc hGu).plusOne) ξ (lixRank n dd + 1))
    (L' : LerayHirschGraded
      (projMapOf ((lixBundle n G hGc hGu).restrictTo (lixKPtSet n k dd i)).plusOne) ξ'
      (lixRank n dd + 1))
    (u : relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd))
    (h : (0 : ℕ) = 2 * lixRank n dd - 2 * ((Fin.last (lixRank n dd) : Fin (lixRank n dd + 1)) : ℕ))
    (htop : ThomChernDeg.thomJmTotalOf K (lixBundle n G hGc hGu) L u (Fin.last (lixRank n dd))
      = cohCast h (one (K := K) (lixN n dd))) :
    (relPullback K (cmap (lixKFibreMap n k dd i hGc hGu)) (lixKFibreMap_mapsTo n k dd i hGc hGu)
      (2 * lixRank n dd)).hom u ≠ 0 := by
  haveI : CompactSpace ↥(lixKPtSet n k dd i) :=
    isCompact_iff_compactSpace.mp isCompact_singleton
  haveI : Nonempty (TopCat.of ↥(lixKPtSet n k dd i)) := ⟨lixKPt n k dd i⟩
  refine lixKFibre_relPullback_ne_zero_of_restrict K n k dd i hGc hGu u ?_
  refine totalInclOn_relPullback_ne_zero_of_top K (lixBundle n G hGc hGu) (lixKPtSet n k dd i)
    hξ L L' u ?_
  rw [htop]
  exact pull_cohCast_one_ne_zeroOf K (inclSubtype (lixKPtSet n k dd i)) h

/-- **The local computation over a field at rank `n`, for a class with unit top coordinate.**
The Leray–Hirsch statement over the singleton at each zero, with its generator compatibility, is an
argument for each zero. -/
theorem kGenLocalNonzeroOf_of_top (K : Type) [Field K] (n k : ℕ) {dd : Fin ℓ → ℕ}
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    {ξ : Hmod K (TopCat.of (Bundle.Proj (lixBundle n G hGc hGu).plusOne)) 2}
    (ξ' : ∀ i : Fin (k + 1), Hmod K (TopCat.of
      (Bundle.Proj ((lixBundle n G hGc hGu).restrictTo (lixKPtSet n k dd i)).plusOne)) 2)
    (hξ : ∀ i : Fin (k + 1),
      pull (cmap (Bundle.projInclOn (lixBundle n G hGc hGu).plusOne (lixKPtSet n k dd i))) 2
        ξ = ξ' i)
    (L : LerayHirschGraded (projMapOf (lixBundle n G hGc hGu).plusOne) ξ (lixRank n dd + 1))
    (L' : ∀ i : Fin (k + 1), LerayHirschGraded
      (projMapOf ((lixBundle n G hGc hGu).restrictTo (lixKPtSet n k dd i)).plusOne) (ξ' i)
      (lixRank n dd + 1))
    (u : relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd))
    (h : (0 : ℕ) = 2 * lixRank n dd - 2 * ((Fin.last (lixRank n dd) : Fin (lixRank n dd + 1)) : ℕ))
    (htop : ThomChernDeg.thomJmTotalOf K (lixBundle n G hGc hGu) L u (Fin.last (lixRank n dd))
      = cohCast h (one (K := K) (lixN n dd))) :
    KGenLocalNonzeroOf K n k hGc hGu hGe u :=
  kGenLocalNonzeroOf_of_fibre K n k hGc hGu hGe u
    (fun i => lixKFibre_ne_zero_of_top K n k dd i hGc hGu (hξ i) L (L' i) u h htop)

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.pull_cohCast_one_ne_zeroOf
#audit_axioms KGen.totalInclOn_relPullback_ne_zero_of_top
#audit_axioms KGen.lixKFibre_ne_zero_of_top
#audit_axioms KGen.kGenLocalNonzeroOf_of_top

end GroupApproximation.CharClass
