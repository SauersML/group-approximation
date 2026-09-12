import GroupApproximation.CharClass.LIXKGenLocalHomotopy
import GroupApproximation.CharClass.LIXKGenLocalRes
import GroupApproximation.CharClass.LIXKGenLocalSplit
import GroupApproximation.CharClass.LIXHsq
import GroupApproximation.Meta.AxiomGuard

/-!
# The compatibility square at the `i`-th zero, at rank `n`

Lane `lx-local2b` (the rank-`n`, `k`-zero port of `CharClass/LIXHsq.lean`).

`CharClass/LIXKGenLocalHomotopy.lean` joins the two legs out of `lixKU`:

* left: `v ↦` the `k`-section at the base chart point of `v`, read through the neighbourhood
  `lixKTrivBall n k dd i` of the `i`-th zero (`lixKGLmap`);
* right: `v ↦` the point of the fibre over `z_i` whose standard-frame coordinate is `v`, read
  through the trivialisation over that neighbourhood (`lixKGRmap`).

This file cuts that homotopy over the `F₂`-line `(lixKU, lixKU ∖ 0)` in the top degree, removes
the far end's linear automorphism (its relative pullback is the identity), and writes both legs as
composites of relative pullbacks.  The left composite passes through `LIXKRelMV.restrictTo` on
`lixKTrivBall`, which is exactly the restriction `KGenLocalNonzero` asks about; the right
composite passes through `lixKRes` and `lixKLocalPairIsoClosed`, where the Thom class is already
known to survive.

## Main results

* `relPullback_lixKFar_eq_lixKGR'` — the far end and the right leg have the same pullback.
* `relPullback_lixKGL_eq_lixKGR` — **the square**: the two legs have the same pullback.
* `relPullback_lixKGL_chain`, `relPullback_lixKGR_chain` — the two legs as chains.
* `lixKExcF_hom_eq` — the excision at the origin is the pullback along `lixKIncF`.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open scoped Matrix
open Set CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ}

/-! ## 1. The far end is the right leg -/

theorem relPullback_lixKFar_eq_lixKGR' (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    relPullback (ZMod 2) (lixKFarMap n k dd i hGc hGu) (lixKFar_mapsTo n k dd i hGc hGu)
        (2 * lixRank n dd)
      = relPullback (ZMod 2) (lixKGRmap' n k dd i hGc hGu) (lixKGR'_mapsTo n k dd i hGc hGu)
        (2 * lixRank n dd) := by
  have e1 : relPullback (ZMod 2) (lixKFarMap n k dd i hGc hGu) (lixKFar_mapsTo n k dd i hGc hGu)
        (2 * lixRank n dd)
      = relPullback (ZMod 2) (lixKGMap n k i hGc hGu ≫ cmap (lixKFibreMap n k dd i hGc hGu))
          (lixKGFibre_mapsTo n k dd i hGc hGu) (2 * lixRank n dd)
        ≫ relPullback (ZMod 2) (lixKShrinkMap n k dd i hGc hGu ≫ lixKIncF n k dd i)
          (lixKSplit_mapsTo n k dd i hGc hGu) (2 * lixRank n dd) :=
    relPullback_comp (ZMod 2) (lixKShrinkMap n k dd i hGc hGu ≫ lixKIncF n k dd i)
      (lixKGMap n k i hGc hGu ≫ cmap (lixKFibreMap n k dd i hGc hGu))
      (lixKSplit_mapsTo n k dd i hGc hGu) (lixKGFibre_mapsTo n k dd i hGc hGu)
      (lixKFar_mapsTo n k dd i hGc hGu) (2 * lixRank n dd)
  have e2 : relPullback (ZMod 2) (lixKGMap n k i hGc hGu ≫ cmap (lixKFibreMap n k dd i hGc hGu))
        (lixKGFibre_mapsTo n k dd i hGc hGu) (2 * lixRank n dd)
      = relPullback (ZMod 2) (cmap (lixKFibreMap n k dd i hGc hGu))
          (lixKFibreMap_mapsTo n k dd i hGc hGu) (2 * lixRank n dd)
        ≫ relPullback (ZMod 2) (lixKGMap n k i hGc hGu) (lixKGHomeo_mapsTo n k i hGc hGu)
          (2 * lixRank n dd) :=
    relPullback_comp (ZMod 2) (lixKGMap n k i hGc hGu) (cmap (lixKFibreMap n k dd i hGc hGu))
      (lixKGHomeo_mapsTo n k i hGc hGu) (lixKFibreMap_mapsTo n k dd i hGc hGu)
      (lixKGFibre_mapsTo n k dd i hGc hGu) (2 * lixRank n dd)
  have e3 : relPullback (ZMod 2) (lixKGRmap' n k dd i hGc hGu) (lixKGR'_mapsTo n k dd i hGc hGu)
        (2 * lixRank n dd)
      = relPullback (ZMod 2) (cmap (lixKFibreMap n k dd i hGc hGu))
          (lixKFibreMap_mapsTo n k dd i hGc hGu) (2 * lixRank n dd)
        ≫ relPullback (ZMod 2) (lixKShrinkMap n k dd i hGc hGu ≫ lixKIncF n k dd i)
          (lixKSplit_mapsTo n k dd i hGc hGu) (2 * lixRank n dd) :=
    relPullback_comp (ZMod 2) (lixKShrinkMap n k dd i hGc hGu ≫ lixKIncF n k dd i)
      (cmap (lixKFibreMap n k dd i hGc hGu)) (lixKSplit_mapsTo n k dd i hGc hGu)
      (lixKFibreMap_mapsTo n k dd i hGc hGu) (lixKGR'_mapsTo n k dd i hGc hGu) (2 * lixRank n dd)
  rw [e1, e2, relPullback_lixKGHomeo_eq_id n k i hGc hGu, Category.comp_id, e3]

/-! ## 2. Cutting the homotopy -/

/-- **The compatibility square at the `i`-th zero**: the two legs have the same pullback. -/
theorem relPullback_lixKGL_eq_lixKGR (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) :
    relPullback (ZMod 2) (lixKGLmap n k dd i hGc hGu hGe) (lixKGL_mapsTo n k dd i hGc hGu hGe)
        (2 * lixRank n dd)
      = relPullback (ZMod 2) (lixKGRmap n k dd i hGc hGu) (lixKGR_mapsTo n k dd i hGc hGu)
        (2 * lixRank n dd) := by
  have hcut : relPullback (ZMod 2) (lixKGLmap n k dd i hGc hGu hGe)
        (lixKGL_mapsTo n k dd i hGc hGu hGe) (2 * lixRank n dd)
      = relPullback (ZMod 2) (lixKFarMap n k dd i hGc hGu) (lixKFar_mapsTo n k dd i hGc hGu)
        (2 * lixRank n dd) :=
    RelativeSupport.relPullback_eq_of_homotopy_of_line contractibleSpace_lixI _ _
      (cmap (lixKHomotopyFun n k dd i hGc hGu)) (lixKHomotopy_mapsTo n k dd i hGc hGu)
      (lixKHomotopy_end_one n k dd i hGc hGu hGe) (lixKHomotopy_end_zero n k dd i hGc hGu)
      (lixKGL_mapsTo n k dd i hGc hGu hGe) (lixKFar_mapsTo n k dd i hGc hGu) (2 * lixRank n dd)
      (by have := two_le_two_mul_lixRank n dd; omega) (lixKULine n k dd i hGc hGu)
  rw [hcut, relPullback_lixKFar_eq_lixKGR' n k dd i hGc hGu,
    relPullback_congr_map (lixKGRmap_eq n k dd i hGc hGu).symm (lixKGR'_mapsTo n k dd i hGc hGu)
      (lixKGR_mapsTo n k dd i hGc hGu) (2 * lixRank n dd)]

/-! ## 3. The two legs as composites of pullbacks -/

/-- **The left leg**: the section's pullback, then the restriction to the neighbourhood of `z_i`,
then the chart point. -/
theorem relPullback_lixKGL_chain (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) :
    relPullback (ZMod 2) (lixKGLmap n k dd i hGc hGu hGe) (lixKGL_mapsTo n k dd i hGc hGu hGe)
        (2 * lixRank n dd)
      = (lixKSRel n k hGc hGu hGe (2 * lixRank n dd)
          ≫ LIXKRelMV.restrictTo (ZMod 2) (X := lixN n dd) (lixKTrivBall n k dd i hGc hGu)
            ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd))
        ≫ relPullback (ZMod 2) (lixKChartPt n k dd i hGc hGu) (lixKChartPt_mapsTo n k dd i hGc hGu)
          (2 * lixRank n dd) := by
  have hbs : ∀ y ∈ ((Subtype.val : ↥(lixKTrivBall n k dd i hGc hGu) → lixN n dd) ⁻¹'
      ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd))),
      (ConcreteCategory.hom (sInclusion (X := lixN n dd) (lixKTrivBall n k dd i hGc hGu)
        ≫ lixKS n k hGc hGu hGe)) y ∈ lixPuncturedInTotal n hGc hGu :=
    fun y hy => lixKSectionTotal_mapsTo n k hGc hGu hGe _ hy
  have s1 : relPullback (ZMod 2) (lixKGLmap n k dd i hGc hGu hGe)
        (lixKGL_mapsTo n k dd i hGc hGu hGe) (2 * lixRank n dd)
      = relPullback (ZMod 2) (sInclusion (X := lixN n dd) (lixKTrivBall n k dd i hGc hGu)
          ≫ lixKS n k hGc hGu hGe) hbs (2 * lixRank n dd)
        ≫ relPullback (ZMod 2) (lixKChartPt n k dd i hGc hGu) (lixKChartPt_mapsTo n k dd i hGc hGu)
          (2 * lixRank n dd) :=
    relPullback_comp (ZMod 2) (lixKChartPt n k dd i hGc hGu)
      (sInclusion (X := lixN n dd) (lixKTrivBall n k dd i hGc hGu) ≫ lixKS n k hGc hGu hGe)
      (lixKChartPt_mapsTo n k dd i hGc hGu) hbs (lixKGL_mapsTo n k dd i hGc hGu hGe)
      (2 * lixRank n dd)
  have s2 : relPullback (ZMod 2) (sInclusion (X := lixN n dd) (lixKTrivBall n k dd i hGc hGu)
        ≫ lixKS n k hGc hGu hGe) hbs (2 * lixRank n dd)
      = lixKSRel n k hGc hGu hGe (2 * lixRank n dd)
        ≫ LIXKRelMV.restrictTo (ZMod 2) (X := lixN n dd) (lixKTrivBall n k dd i hGc hGu)
          ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd) :=
    relPullback_comp (ZMod 2) (sInclusion (X := lixN n dd) (lixKTrivBall n k dd i hGc hGu))
      (lixKS n k hGc hGu hGe)
      (LIXKRelMV.sInclusion_mapsTo_preimage (X := lixN n dd) (lixKTrivBall n k dd i hGc hGu)
        ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd)))
      (lixKSectionTotal_mapsTo n k hGc hGu hGe) hbs (2 * lixRank n dd)
  -- the composite's middle object is spelled over `↥sphereOne × baseM` on one side and over the
  -- carrier of `lixN n dd` on the other, so the closing `rfl` needs default transparency
  rw [s1, s2]
  rfl

/-- **The right leg**: the restriction of the bundle pair to the neighbourhood of `z_i`, the
trivialisation, the slice at `z_i`, the excision at the origin, and the shrink to `lixKU`. -/
theorem relPullback_lixKGR_chain (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    relPullback (ZMod 2) (lixKGRmap n k dd i hGc hGu) (lixKGR_mapsTo n k dd i hGc hGu)
        (2 * lixRank n dd)
      = (relPullback (ZMod 2) (lixKInclOn n k dd i hGc hGu) (lixKInclOn_mapsTo n k dd i hGc hGu)
            (2 * lixRank n dd)
          ≫ relPullback (ZMod 2) (lixKTrivInv n k dd i hGc hGu)
            (lixKTrivInv_mapsTo n k dd i hGc hGu) (2 * lixRank n dd)
          ≫ relPullback (ZMod 2)
            (RelativeSupport.sliceMap (lixKZeroInBall n k dd i hGc hGu) (Fin (lixRank n dd) → ℂ))
            (RelativeSupport.slice_mapsTo (lixKZeroInBall n k dd i hGc hGu)
              (puncturedSet (lixRank n dd))) (2 * lixRank n dd)
          ≫ relPullback (ZMod 2) (lixKIncF n k dd i) (lixKIncF_mapsTo n k dd i)
            (2 * lixRank n dd))
        ≫ relPullback (ZMod 2) (lixKShrinkMap n k dd i hGc hGu)
          (lixKShrink_mapsTo n k dd i hGc hGu) (2 * lixRank n dd) := by
  have hti : ∀ q ∈ {q : ↥(lixKTrivBall n k dd i hGc hGu) × (Fin (lixRank n dd) → ℂ) | q.2 ≠ 0},
      (ConcreteCategory.hom (lixKTrivInv n k dd i hGc hGu ≫ lixKInclOn n k dd i hGc hGu)) q
        ∈ lixPuncturedInTotal n hGc hGu :=
    fun q hq => lixKInclOn_mapsTo n k dd i hGc hGu _ (lixKTrivInv_mapsTo n k dd i hGc hGu q hq)
  have hsti : ∀ y ∈ puncturedSet (lixRank n dd),
      (ConcreteCategory.hom (RelativeSupport.sliceMap (lixKZeroInBall n k dd i hGc hGu)
        (Fin (lixRank n dd) → ℂ) ≫ (lixKTrivInv n k dd i hGc hGu ≫ lixKInclOn n k dd i hGc hGu))) y
        ∈ lixPuncturedInTotal n hGc hGu :=
    fun y hy => hti _ (RelativeSupport.slice_mapsTo (lixKZeroInBall n k dd i hGc hGu)
      (puncturedSet (lixRank n dd)) y hy)
  have hfsti : ∀ x ∈ ((Subtype.val : ↥(lixKFC n k dd i).target → (Fin (lixRank n dd) → ℂ)) ⁻¹'
      ({(0 : Fin (lixRank n dd) → ℂ)}ᶜ)),
      (ConcreteCategory.hom (lixKIncF n k dd i ≫ (RelativeSupport.sliceMap
        (lixKZeroInBall n k dd i hGc hGu) (Fin (lixRank n dd) → ℂ) ≫
        (lixKTrivInv n k dd i hGc hGu ≫ lixKInclOn n k dd i hGc hGu)))) x
        ∈ lixPuncturedInTotal n hGc hGu :=
    fun x hx => hsti _ (lixKIncF_mapsTo n k dd i x hx)
  have s1 : relPullback (ZMod 2) (lixKGRmap n k dd i hGc hGu) (lixKGR_mapsTo n k dd i hGc hGu)
        (2 * lixRank n dd)
      = relPullback (ZMod 2) (lixKIncF n k dd i ≫ (RelativeSupport.sliceMap
          (lixKZeroInBall n k dd i hGc hGu) (Fin (lixRank n dd) → ℂ) ≫
          (lixKTrivInv n k dd i hGc hGu ≫ lixKInclOn n k dd i hGc hGu))) hfsti (2 * lixRank n dd)
        ≫ relPullback (ZMod 2) (lixKShrinkMap n k dd i hGc hGu)
          (lixKShrink_mapsTo n k dd i hGc hGu) (2 * lixRank n dd) :=
    relPullback_comp (ZMod 2) (lixKShrinkMap n k dd i hGc hGu) _
      (lixKShrink_mapsTo n k dd i hGc hGu) hfsti (lixKGR_mapsTo n k dd i hGc hGu) (2 * lixRank n dd)
  have s2 : relPullback (ZMod 2) (lixKIncF n k dd i ≫ (RelativeSupport.sliceMap
        (lixKZeroInBall n k dd i hGc hGu) (Fin (lixRank n dd) → ℂ) ≫
        (lixKTrivInv n k dd i hGc hGu ≫ lixKInclOn n k dd i hGc hGu))) hfsti (2 * lixRank n dd)
      = relPullback (ZMod 2) (RelativeSupport.sliceMap (lixKZeroInBall n k dd i hGc hGu)
          (Fin (lixRank n dd) → ℂ) ≫ (lixKTrivInv n k dd i hGc hGu ≫ lixKInclOn n k dd i hGc hGu))
          hsti (2 * lixRank n dd)
        ≫ relPullback (ZMod 2) (lixKIncF n k dd i) (lixKIncF_mapsTo n k dd i) (2 * lixRank n dd) :=
    relPullback_comp (ZMod 2) (lixKIncF n k dd i) _ (lixKIncF_mapsTo n k dd i) hsti hfsti
      (2 * lixRank n dd)
  have s3 : relPullback (ZMod 2) (RelativeSupport.sliceMap (lixKZeroInBall n k dd i hGc hGu)
        (Fin (lixRank n dd) → ℂ) ≫ (lixKTrivInv n k dd i hGc hGu ≫ lixKInclOn n k dd i hGc hGu))
        hsti (2 * lixRank n dd)
      = relPullback (ZMod 2) (lixKTrivInv n k dd i hGc hGu ≫ lixKInclOn n k dd i hGc hGu) hti
          (2 * lixRank n dd)
        ≫ relPullback (ZMod 2)
          (RelativeSupport.sliceMap (lixKZeroInBall n k dd i hGc hGu) (Fin (lixRank n dd) → ℂ))
          (RelativeSupport.slice_mapsTo (lixKZeroInBall n k dd i hGc hGu)
            (puncturedSet (lixRank n dd))) (2 * lixRank n dd) :=
    relPullback_comp (ZMod 2)
      (RelativeSupport.sliceMap (lixKZeroInBall n k dd i hGc hGu) (Fin (lixRank n dd) → ℂ)) _
      (RelativeSupport.slice_mapsTo (lixKZeroInBall n k dd i hGc hGu) (puncturedSet (lixRank n dd)))
      hti hsti (2 * lixRank n dd)
  have s4 : relPullback (ZMod 2) (lixKTrivInv n k dd i hGc hGu ≫ lixKInclOn n k dd i hGc hGu) hti
        (2 * lixRank n dd)
      = relPullback (ZMod 2) (lixKInclOn n k dd i hGc hGu) (lixKInclOn_mapsTo n k dd i hGc hGu)
          (2 * lixRank n dd)
        ≫ relPullback (ZMod 2) (lixKTrivInv n k dd i hGc hGu) (lixKTrivInv_mapsTo n k dd i hGc hGu)
          (2 * lixRank n dd) :=
    relPullback_comp (ZMod 2) (lixKTrivInv n k dd i hGc hGu) (lixKInclOn n k dd i hGc hGu)
      (lixKTrivInv_mapsTo n k dd i hGc hGu) (lixKInclOn_mapsTo n k dd i hGc hGu) hti
      (2 * lixRank n dd)
  rw [s1, s2, s3, s4]
  simp only [Category.assoc]

/-! ## 4. The identifications, one at a time

Each is `rfl`.  They are stated separately so that a consumer rewrites along named pullbacks
instead of asking the elaborator to unfold several isomorphisms at once. -/

theorem lixKRes_eq (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    lixKRes n k dd i hGc hGu (2 * lixRank n dd)
      = relPullback (ZMod 2) (lixKInclOn n k dd i hGc hGu) (lixKInclOn_mapsTo n k dd i hGc hGu)
        (2 * lixRank n dd) := rfl

theorem lixKBundlePairIso_hom_eq (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    (lixKBundlePairIso n k dd i hGc hGu (2 * lixRank n dd)).hom
      = relPullback (ZMod 2) (lixKTrivInv n k dd i hGc hGu) (lixKTrivInv_mapsTo n k dd i hGc hGu)
        (2 * lixRank n dd) := rfl

theorem lixKProdIso_hom_eq (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    (RelativeSupport.relCohomologyProdIso (contractibleSpace_lixKTrivBall n k dd i hGc hGu)
        (lixKZeroInBall n k dd i hGc hGu) (lixRank n dd) (2 * lixRank n dd)
        (two_le_two_mul_lixRank n dd)).hom
      = relPullback (ZMod 2)
          (RelativeSupport.sliceMap (lixKZeroInBall n k dd i hGc hGu) (Fin (lixRank n dd) → ℂ))
          (RelativeSupport.slice_mapsTo (lixKZeroInBall n k dd i hGc hGu)
            (puncturedSet (lixRank n dd))) (2 * lixRank n dd) := rfl

theorem lixKLocalPairIsoClosed_hom_eq (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    (lixKLocalPairIsoClosed n k dd i hGc hGu).hom
      = (lixKBundlePairIso n k dd i hGc hGu (2 * lixRank n dd)).hom
        ≫ (RelativeSupport.relCohomologyProdIso (contractibleSpace_lixKTrivBall n k dd i hGc hGu)
          (lixKZeroInBall n k dd i hGc hGu) (lixRank n dd) (2 * lixRank n dd)
          (two_le_two_mul_lixRank n dd)).hom := rfl

/-- **The excision at the origin is the pullback along `lixKIncF`.** -/
theorem lixKExcF_hom_eq (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    (excisionIsoPoint (TopCat.of (Fin (lixRank n dd) → ℂ)) (0 : Fin (lixRank n dd) → ℂ)
        (lixKFC n k dd i).target (lixKFC n k dd i).open_target (zero_mem_lixKFC_target n k dd i)
        (2 * lixRank n dd)).hom
      = relPullback (ZMod 2) (lixKIncF n k dd i) (lixKIncF_mapsTo n k dd i) (2 * lixRank n dd) :=
  rfl

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.relPullback_lixKFar_eq_lixKGR'
#audit_axioms KGen.relPullback_lixKGL_eq_lixKGR
#audit_axioms KGen.relPullback_lixKGL_chain
#audit_axioms KGen.relPullback_lixKGR_chain

end GroupApproximation.CharClass
