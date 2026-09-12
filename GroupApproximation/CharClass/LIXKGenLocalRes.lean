import GroupApproximation.CharClass.LIXKGenLocalPair
import GroupApproximation.CharClass.LIXKGenThomTerm
import GroupApproximation.CharClass.LIXResFibre
import GroupApproximation.Meta.AxiomGuard

/-!
# `hres` at the `i`-th zero, at rank `n`: the Thom class survives restriction to the neighbourhood

Lane `lix-oddside-n` (chart side of `KGenLocalNonzero`).

This is the rank-`n`, `k`-zero counterpart of `CharClass/LIXRestrictionMap.lean`'s `lixRes` and
`CharClass/LIXResFibre.lean`'s `lixRes_lixThomClassTerm_ne_zero`, over
`CharClass/LIXKGenLocalPair.lean`'s neighbourhood `lixKTrivBall n k dd i` of the `i`-th zero.

The route is the rank-two one.  The restriction to the ball cannot be computed where it lives,
because `thomJmTotal` needs a compact Hausdorff base; so the class is followed one step further,
to the fibre over `z_i`, whose base is a point.  Restricting to the point factors through
restricting to the ball (`relPullback_totalInclOn_sub`, generic), the coordinates restrict
coordinatewise (`thomJmTotal_restrict`, generic), and the top coordinate of the Thom class is the
unit of `H^0` (`KGen.thomJmTotal_lixThomClassTerm`), which restricts to the unit of a point.

## Main declarations

* `KGen.lixKRes n k dd i hGc hGu q` — restriction of the bundle pair to the neighbourhood of `z_i`.
* `KGen.pull_lixTopCoeff_ne_zero` — the top coefficient survives any restriction.
* `KGen.lixKRes_lixThomClassTerm_ne_zero` — **the Thom class survives the restriction.**
* `KGen.lixKLocalPairIsoClosed_lixKRes_ne_zero` — its image in the local model is nonzero.
-/

open CategoryTheory TopologicalSpace
open GroupApproximation.STW59
open GroupApproximation.CharClass.LH
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

namespace KGen

noncomputable section

set_option linter.unusedSectionVars false

variable {ℓ : ℕ}

/-- **The restriction of the bundle pair to the neighbourhood of the `i`-th zero.** -/
def lixKRes (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) (q : ℕ) :
    relCohomology (ZMod 2) (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu) q ⟶
      relCohomology (ZMod 2)
        (TopCat.of (Bundle.Total
          ((lixBundle n G hGc hGu).restrictTo (lixKTrivBall n k dd i hGc hGu))))
        {w : Bundle.Total ((lixBundle n G hGc hGu).restrictTo (lixKTrivBall n k dd i hGc hGu)) |
          (w : ↥(lixKTrivBall n k dd i hGc hGu) × (Gen.VIdx n dd ⊕ Gen.VIdx n dd → ℂ))
            ∈ Bundle.puncturedSet
              ((lixBundle n G hGc hGu).restrictTo (lixKTrivBall n k dd i hGc hGu))} q :=
  relPullback (ZMod 2)
    (cmap (Bundle.totalInclOn (lixBundle n G hGc hGu) (lixKTrivBall n k dd i hGc hGu)))
    (totalInclOn_mapsTo _ _) q

/-- **The generator of the top coefficient group restricts to a nonzero class.** -/
theorem pull_lixTopCoeff_ne_zero (n : ℕ) (dd : Fin ℓ → ℕ) {Y : TopCat.{0}} [Nonempty Y]
    (f : Y ⟶ lixN n dd) :
    pull f (2 * lixRank n dd - 2 * lixRank n dd) (lixTopCoeff n dd) ≠ 0 := by
  show pull f (2 * lixRank n dd - 2 * lixRank n dd)
      (cohCast (show (0 : ℕ) = 2 * lixRank n dd - 2 * lixRank n dd by omega)
        (one (lixN n dd))) ≠ 0
  rw [LH.pull_cohCast, pull_one]
  exact ThomChernDeg.cohCast_ne_zero _ (one_ne_zero_cohZero Y)

set_option maxHeartbeats 1000000 in
/-- **The Thom class survives the restriction to the neighbourhood of `z_i`.** -/
theorem lixKRes_lixThomClassTerm_ne_zero (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    (lixKRes n k dd i hGc hGu (2 * lixRank n dd)).hom (lixThomClassTerm n hGc hGu) ≠ 0 := by
  haveI hnW : Nonempty ↥({lixKZero n k dd i} : Set (↥sphereOne × Gen.baseM n dd)) :=
    ⟨⟨lixKZero n k dd i, rfl⟩⟩
  haveI hnW' : Nonempty
      (TopCat.of ↥({lixKZero n k dd i} : Set (↥sphereOne × Gen.baseM n dd))) :=
    ⟨⟨lixKZero n k dd i, rfl⟩⟩
  haveI hcW : CompactSpace ↥({lixKZero n k dd i} : Set (↥sphereOne × Gen.baseM n dd)) :=
    isCompact_iff_compactSpace.mp isCompact_singleton
  intro h0
  have hzb : lixKZero n k dd i ∈ lixKTrivBall n k dd i hGc hGu :=
    lixKZero_mem_lixKTrivBall n k dd i hGc hGu
  have hWU : ({lixKZero n k dd i} : Set (↥sphereOne × Gen.baseM n dd))
      ⊆ lixKTrivBall n k dd i hGc hGu :=
    Set.singleton_subset_iff.mpr hzb
  have hrankW : ∀ x : ↥({lixKZero n k dd i} : Set (↥sphereOne × Gen.baseM n dd)),
      (((lixBundle n G hGc hGu).restrictTo
        ({lixKZero n k dd i} : Set (↥sphereOne × Gen.baseM n dd))).plusOne).rank x
        = lixRank n dd + 1 := fun x => rank_lixBundle_plusOne n G hGc hGu _
  have LW : LerayHirschGraded
      (projMapOf (((lixBundle n G hGc hGu).restrictTo
        ({lixKZero n k dd i} : Set (↥sphereOne × Gen.baseM n dd))).plusOne))
      (tautEulerOf (((lixBundle n G hGc hGu).restrictTo
        ({lixKZero n k dd i} : Set (↥sphereOne × Gen.baseM n dd))).plusOne))
      (lixRank n dd + 1) :=
    lerayHirschGraded_compact _ (lixRank n dd + 1) hrankW (Nat.succ_le_succ (Nat.zero_le _))
  have hcoord := thomJmTotal_restrict (lixBundle n G hGc hGu)
    ({lixKZero n k dd i} : Set (↥sphereOne × Gen.baseM n dd)) (lixLHplus n hGc hGu) LW
    (lixThomClassTerm n hGc hGu)
  have h0' : (relPullback (ZMod 2) (cmap (Bundle.totalInclOn (lixBundle n G hGc hGu)
        (lixKTrivBall n k dd i hGc hGu))) (totalInclOn_mapsTo _ _) (2 * lixRank n dd)).hom
      (lixThomClassTerm n hGc hGu) = 0 := h0
  have hzeroW : (relPullback (ZMod 2) (cmap (Bundle.totalInclOn (lixBundle n G hGc hGu)
        ({lixKZero n k dd i} : Set (↥sphereOne × Gen.baseM n dd)))) (totalInclOn_mapsTo _ _)
      (2 * lixRank n dd)).hom (lixThomClassTerm n hGc hGu) = 0 := by
    rw [relPullback_totalInclOn_sub (lixBundle n G hGc hGu) hWU (2 * lixRank n dd)]
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    rw [h0', map_zero]
  have htop : ThomChernDeg.thomJmTotal (lixBundle n G hGc hGu) (lixLHplus n hGc hGu)
        (lixThomClassTerm n hGc hGu) (Fin.last (lixRank n dd))
      = lixTopCoeff n dd := by
    rw [thomJmTotal_lixThomClassTerm n hGc hGu]
    exact ThomDeg.thomLift_last _ _
  have hfin := congrFun hcoord (Fin.last (lixRank n dd))
  simp only [hzeroW, map_zero, Pi.zero_apply, htop] at hfin
  exact pull_lixTopCoeff_ne_zero n dd
    (inclSubtype ({lixKZero n k dd i} : Set (↥sphereOne × Gen.baseM n dd))) hfin.symm

/-- **The restricted Thom class is nonzero in the local model.** -/
theorem lixKLocalPairIsoClosed_lixKRes_ne_zero (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    (lixKLocalPairIsoClosed n k dd i hGc hGu).hom
        ((lixKRes n k dd i hGc hGu (2 * lixRank n dd)).hom (lixThomClassTerm n hGc hGu)) ≠ 0 := by
  intro h
  refine lixKRes_lixThomClassTerm_ne_zero n k dd i hGc hGu ?_
  rw [← iso_inv_hom_apply (lixKLocalPairIsoClosed n k dd i hGc hGu)
    ((lixKRes n k dd i hGc hGu (2 * lixRank n dd)).hom (lixThomClassTerm n hGc hGu)), h,
    map_zero]

end

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.lixKRes_lixThomClassTerm_ne_zero
#audit_axioms KGen.lixKLocalPairIsoClosed_lixKRes_ne_zero

end GroupApproximation.CharClass
