import GroupApproximation.CharClass.ThomChartSquare
import GroupApproximation.CharClass.ThomBridgeTotal
import GroupApproximation.CharClass.LIXThomClassTerm
import GroupApproximation.CharClass.ChernSliceNaturality
import GroupApproximation.CharClass.CohomologyLHRestrict
import GroupApproximation.CharClass.RelativeHomotopyInvariance

/-!
# The Thom coordinates are natural in the base

Lane `lix-hres` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`ThomBridgeTotal` recorded, in its own docstring, that publishing `bridgeTotal` as
a bare isomorphism is a defect: a consumer who has to *compute* through it finds
no lemma.  `ThomChartSquare` repaired that for the bridge itself.  This file
repairs it for the coordinate map `thomJmTotal`, which is what the Thom class is
named by.

The statement is that the Leray–Hirsch coordinates of a class of the
vector-bundle pair restrict, coordinate by coordinate, to the coordinates of its
restriction:

```text
thomJmTotal (p|_U) L' (res x) i  =  (incl U)^* (thomJmTotal p L x i).
```

Three things go into it and nothing else: the bridge's naturality
(`bridgeTotalRestrict`), naturality of `j^*` (`relToAbs_naturality`), and the fact
that a Leray–Hirsch column term pulls back to the column term at the same index
over the new base (`pull_lhTerm_base`, one line on top of `LHCast.pull_lhTerm`).
The two topological inputs of the last are `cc-projective`'s `projComap_square`
and `tautEulerOf_comap`, both of which are already **general base change**, not
merely restriction.

**What this does not do.**  It computes coordinates; it says nothing about
whether the restricted class is nonzero, which needs a coordinate that survives,
and that is the consumer's business.  It also does not reach a part of the base
that is not compact Hausdorff: `thomJmTotal` needs `bridgeTotal`, which needs a
compact Hausdorff base, so none of this applies over a ball.

## Main declarations

* `LH.pull_lhTerm_base` — a column term under a base change.
* `thomJm_natural` — **the coordinates of `thomJm` are natural.**
* `thomJmTotal_restrict` — **the coordinates of `thomJmTotal` under a base
  restriction.**
-/

open CategoryTheory TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

set_option linter.unusedSectionVars false

/-! ## 1. A column term under a base change -/

namespace LH

/-- **A Leray–Hirsch column term pulls back to the column term at the same index**,
along a map of projections over a map of bases.  `LHCast.pull_lhTerm` is the case
of a fixed base; the base change is one `pull_comp` on the coefficient. -/
theorem pull_lhTerm_base {X X' P P' : TopCat.{0}} (g : P' ⟶ P) (fb : X' ⟶ X)
    (π : P ⟶ X) (π' : P' ⟶ X') (hsq : g ≫ π = π' ≫ fb)
    (ξ : Hmod2 P 2) (ξ' : Hmod2 P' 2) (hξ : pull g 2 ξ = ξ')
    (n i : ℕ) (a : Hmod2 X (n - 2 * i)) :
    pull g n (lhTerm π ξ n i a) = lhTerm π' ξ' n i (pull fb (n - 2 * i) a) := by
  rw [LHCast.pull_lhTerm g π (π' ≫ fb) hsq ξ ξ' hξ n i a]
  by_cases hi : 2 * i ≤ n
  · rw [lhTerm_of_le (π' ≫ fb) ξ' hi, lhTerm_of_le π' ξ' hi, pull_comp]
  · rw [lhTerm_of_gt (π' ≫ fb) ξ' hi, lhTerm_of_gt π' ξ' hi]

end LH

/-! ## 2. Naturality of the coordinate map -/

open LH

set_option maxHeartbeats 1000000 in
/-- **The Leray–Hirsch coordinates of a relative class are natural.**  Both sides
of the square are determined by the same combination of column terms, so nothing
about exactness enters: it is `relToAbs_naturality` followed by `pull_lhTerm_base`
inside the sum, read back through the coordinate equivalence. -/
theorem thomJm_natural {X X' P P' : TopCat.{0}} {π : P ⟶ X} {ξ : Hmod2 P 2}
    {π' : P' ⟶ X'} {ξ' : Hmod2 P' 2} {r : ℕ}
    (L : LerayHirschGraded π ξ (r + 1)) (L' : LerayHirschGraded π' ξ' (r + 1))
    (g : P' ⟶ P) (fb : X' ⟶ X) (hsq : g ≫ π = π' ≫ fb) (hξ : pull g 2 ξ = ξ')
    {Z : Set P} {Z' : Set P'} (hZ : ∀ z ∈ Z', (ConcreteCategory.hom g) z ∈ Z)
    (x : ↥(relCohomology (ZMod 2) P Z (2 * r))) :
    thomJm L' Z' ((relPullback (ZMod 2) g hZ (2 * r)).hom x)
      = fun i : Fin (r + 1) => pull fb (2 * r - 2 * (i : ℕ)) (thomJm L Z x i) := by
  have hrel : (relToAbs (ZMod 2) P' Z' (2 * r)).hom
        ((relPullback (ZMod 2) g hZ (2 * r)).hom x)
      = pull g (2 * r) ((relToAbs (ZMod 2) P Z (2 * r)).hom x) := by
    have h := RelativeSupport.linearMap_comp_of_square
      (relToAbs_naturality (ZMod 2) g hZ (2 * r))
    have h2 := LinearMap.congr_fun h x
    simp only [LinearMap.comp_apply] at h2
    -- the ambient pullback of a map of pairs **is** `pull`, definitionally
    exact h2
  have hL : lhSumTop π ξ r (thomJm L Z x) = (relToAbs (ZMod 2) P Z (2 * r)).hom x := by
    show (lhTopEquiv L) (thomJm L Z x) = _
    exact (lhTopEquiv L).apply_symm_apply _
  have hsum : lhSumTop π' ξ' r
        (fun i : Fin (r + 1) => pull fb (2 * r - 2 * (i : ℕ)) (thomJm L Z x i))
      = (relToAbs (ZMod 2) P' Z' (2 * r)).hom
          ((relPullback (ZMod 2) g hZ (2 * r)).hom x) := by
    rw [hrel, ← hL, lhSumTop_apply, lhSumTop_apply, pull_sum]
    exact Finset.sum_congr rfl fun (i : Fin (r + 1)) _ =>
      (pull_lhTerm_base g fb π π' hsq ξ ξ' hξ (2 * r) (i : ℕ) (thomJm L Z x i)).symm
  show (lhTopEquiv L').symm ((relToAbs (ZMod 2) P' Z' (2 * r)).hom
      ((relPullback (ZMod 2) g hZ (2 * r)).hom x)) = _
  rw [← hsum]
  exact (lhTopEquiv L').symm_apply_apply _

/-! ## 3. At the vector-bundle pair, under a base restriction -/

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The inclusion of the restricted projectivisation **is** the base change of
projective bundles, so `cc-projective`'s two naturality facts apply to it
verbatim. -/
theorem projInclOn_eq_projComap (p : Bundle X ι) (U : Set X) :
    Bundle.projInclOn p U
      = Bundle.projComap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X)) p := rfl

/-- The projection square of the restricted projectivisation.  By `rfl` on points:
both routes read off the base point and forget that it lies in `U`. -/
theorem projInclOn_proj_square (p : Bundle X ι) (U : Set X) :
    cmap (Bundle.projInclOn p.plusOne U) ≫ projMapOf p.plusOne
      = projMapOf ((p.restrictTo U).plusOne) ≫ inclSubtype U := by
  apply TopCat.Hom.ext
  exact ContinuousMap.ext fun _ => rfl

/-- The tautological class of the restricted projectivised sum is the pullback of
the tautological class.  `cc-projective`'s `tautEulerOf_comap`, at the inclusion. -/
theorem pull_projInclOn_tautEulerOf (p : Bundle X ι) (U : Set X) :
    pull (cmap (Bundle.projInclOn p.plusOne U)) 2 (tautEulerOf p.plusOne)
      = tautEulerOf ((p.restrictTo U).plusOne) :=
  LH.tautEulerOf_comap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X)) p.plusOne

set_option maxHeartbeats 1000000 in
/-- **The Thom coordinates under a base restriction.**  Coordinate by coordinate,
the coordinates of the restricted class are the restrictions of the coordinates.

This is the lemma `ThomBridgeTotal`'s docstring said did not exist: it is what
lets a class be pushed across the bridge and then compared with something on the
other side. -/
theorem thomJmTotal_restrict [CompactSpace X] [T2Space X] (p : Bundle X ι)
    (U : Set X) [CompactSpace ↥U] [T2Space ↥U] {r : ℕ}
    (L : LerayHirschGraded (projMapOf p.plusOne) (tautEulerOf p.plusOne) (r + 1))
    (L' : LerayHirschGraded (projMapOf ((p.restrictTo U).plusOne))
      (tautEulerOf ((p.restrictTo U).plusOne)) (r + 1))
    (x : ↥(relCohomology (ZMod 2) (TopCat.of (Bundle.Total p))
      ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p)
      (2 * r))) :
    ThomChernDeg.thomJmTotal (p.restrictTo U) L'
        ((relPullback (ZMod 2) (cmap (Bundle.totalInclOn p U))
          (totalInclOn_mapsTo p U) (2 * r)).hom x)
      = fun i : Fin (r + 1) => pull (inclSubtype U) (2 * r - 2 * (i : ℕ))
          (ThomChernDeg.thomJmTotal p L x i) :=
  ((ThomChernDeg.thomJmTotal_apply (p.restrictTo U) L'
        ((relPullback (ZMod 2) (cmap (Bundle.totalInclOn p U))
          (totalInclOn_mapsTo p U) (2 * r)).hom x)).trans
      (congrArg
        (fun z => thomJm L' (Set.range (Bundle.projIncl (p.restrictTo U))) z)
        (bridgeTotalRestrict p U (2 * r) x).symm)).trans
    (thomJm_natural L L' (cmap (Bundle.projInclOn p.plusOne U)) (inclSubtype U)
      (projInclOn_proj_square p U) (pull_projInclOn_tautEulerOf p U)
      (fun z hz => projInclOn_range_mapsTo p U z hz)
      (ThomChernDeg.bridgeTotal p (2 * r) x))

/-! Printed on every build. -/

#print axioms thomJmTotal_restrict

end

end GroupApproximation.CharClass
