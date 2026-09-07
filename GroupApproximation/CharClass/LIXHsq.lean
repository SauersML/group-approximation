import GroupApproximation.CharClass.LIXHsqLegs

/-!
# `hsq`, the compatibility square of Step C's odd side

Lane `lix-hsq`.

The square asserts that sectioning then charting agrees with restricting then trivialising:

```text
lixSRel ≫ lixRelModelIso.hom = lixRes ≫ lixLocalPairIsoClosed.hom
```

Both outer legs are relative pullbacks, but `lixRelModelIso` contains an **inverse**
excision, so the square cannot be checked pointwise end to end.  Composing that excision's
forward map onto both sides removes the inverse, and restricting further to `lixU` — which
loses nothing, by excision at the origin — makes both sides pullbacks along explicit maps of
pairs out of `lixU`:

* left: `v ↦ the section at the chart point of v`;
* right: `v ↦ the point of the fibre over the section's zero with frame coordinate v`.

`LIXHsqHomotopy` joins them by a homotopy through maps of pairs whose far end is the right
leg precomposed with the linear automorphism `lixKLin`, and `RelativeLineHomotopy` cuts that
homotopy at either end because the relative group of `(lixU, lixU ∖ 0)` is a line.  The
automorphism's own pullback is the identity for the same reason.

## What is proved and what is not

`lixHsq` is the `hsq` binder of `lix_topClass_ne_zero_of_thom`, character for character, over
`hGc`, `hGu`, `hGe` and nothing else.  It does **not** prove `hres`, and the argument never
needs it: the two legs are shown **equal**, not both nonzero.

That distinction is worth stating precisely, because the loose version of it overstates.
Both legs are maps between `F₂`-lines — the source by `ThomChernDeg.lixRelLine`, the target
by `localEquiv` — so equality *would* also follow from both being nonzero, and that is the
route this lane did not take.  On the right, "nonzero" is `hres` exactly, since a map out of
a line is nonzero iff injective.  On the left it is injectivity of `lixSRel ≫ t`, which is
**not** Step C's conclusion — that is `gamma ≠ 0` — but the hypothesis `hinj` that Step C's
odd side consumes, and so precisely the statement the square together with `hres` exists to
produce.  A "both nonzero" proof would therefore have had to supply the reduction's own
output by independent means: not a logical circle, but a reduction that assumes what it was
introduced to give.  Shown equal, neither leg's nonvanishing is needed at all.

`lix_topClass_ne_zero_of_thom` is deliberately not imported: the square mentions none of its
Thom-class layer, and importing it would drag the whole Leray–Hirsch closure into a module
that needs four definitions.

## Main results

* `lixHsq_shrunk` — the square after the excision and the restriction to `lixU`.
* `lixHsq` — **the compatibility square**.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open Set CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-! ## 1. Transporting a pullback along an equality of maps -/

/-- The relative pullback depends on the map and not on the proof that it is a map of pairs,
so an equality of maps transports it.  Stated rather than used through `▸`, which puts the
transported proof into the statement and then blocks the next rewrite. -/
theorem relPullback_congr_map {X Y : TopCat.{0}} {A : Set X} {B : Set Y} {f g : X ⟶ Y}
    (h : f = g) (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B)
    (hg : ∀ x ∈ A, (ConcreteCategory.hom g) x ∈ B) (n : ℕ) :
    relPullback (ZMod 2) f hf n = relPullback (ZMod 2) g hg n := by
  subst h
  rfl

/-! ## 2. The far end is the right leg -/

theorem relPullback_lixFar_eq_lixGR' (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    relPullback (ZMod 2) (lixFarMap hGc hGu) (lixFar_mapsTo hGc hGu) (2 * lixRank dd)
      = relPullback (ZMod 2) (lixGRmap' hGc hGu) (lixGR'_mapsTo hGc hGu)
        (2 * lixRank dd) := by
  have e1 : relPullback (ZMod 2) (lixFarMap hGc hGu) (lixFar_mapsTo hGc hGu)
        (2 * lixRank dd)
      = relPullback (ZMod 2) (lixKMap hGc hGu ≫ cmap (lixFibreMap hGc hGu))
          (lixKFibre_mapsTo hGc hGu) (2 * lixRank dd)
        ≫ relPullback (ZMod 2) (lixShrinkMap hGc hGu ≫ lixIncF dd)
          (lixSplit_mapsTo hGc hGu) (2 * lixRank dd) :=
    relPullback_comp (ZMod 2) (lixShrinkMap hGc hGu ≫ lixIncF dd)
      (lixKMap hGc hGu ≫ cmap (lixFibreMap hGc hGu)) (lixSplit_mapsTo hGc hGu)
      (lixKFibre_mapsTo hGc hGu) (lixFar_mapsTo hGc hGu) (2 * lixRank dd)
  have e2 : relPullback (ZMod 2) (lixKMap hGc hGu ≫ cmap (lixFibreMap hGc hGu))
        (lixKFibre_mapsTo hGc hGu) (2 * lixRank dd)
      = relPullback (ZMod 2) (cmap (lixFibreMap hGc hGu)) (lixFibreMap_mapsTo hGc hGu)
          (2 * lixRank dd)
        ≫ relPullback (ZMod 2) (lixKMap hGc hGu) (lixKHomeo_mapsTo hGc hGu)
          (2 * lixRank dd) :=
    relPullback_comp (ZMod 2) (lixKMap hGc hGu) (cmap (lixFibreMap hGc hGu))
      (lixKHomeo_mapsTo hGc hGu) (lixFibreMap_mapsTo hGc hGu) (lixKFibre_mapsTo hGc hGu)
      (2 * lixRank dd)
  have e3 : relPullback (ZMod 2) (lixGRmap' hGc hGu) (lixGR'_mapsTo hGc hGu)
        (2 * lixRank dd)
      = relPullback (ZMod 2) (cmap (lixFibreMap hGc hGu)) (lixFibreMap_mapsTo hGc hGu)
          (2 * lixRank dd)
        ≫ relPullback (ZMod 2) (lixShrinkMap hGc hGu ≫ lixIncF dd)
          (lixSplit_mapsTo hGc hGu) (2 * lixRank dd) :=
    relPullback_comp (ZMod 2) (lixShrinkMap hGc hGu ≫ lixIncF dd)
      (cmap (lixFibreMap hGc hGu)) (lixSplit_mapsTo hGc hGu) (lixFibreMap_mapsTo hGc hGu)
      (lixGR'_mapsTo hGc hGu) (2 * lixRank dd)
  rw [e1, e2, relPullback_lixKHomeo_eq_id hGc hGu, Category.comp_id, e3]

/-! ## 3. Cutting the homotopy -/

theorem relPullback_lixGL_eq_lixGR (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) :
    relPullback (ZMod 2) (lixGLmap hGc hGu hGe) (lixGL_mapsTo hGc hGu hGe)
        (2 * lixRank dd)
      = relPullback (ZMod 2) (lixGRmap hGc hGu) (lixGR_mapsTo hGc hGu)
        (2 * lixRank dd) := by
  have hcut : relPullback (ZMod 2) (lixGLmap hGc hGu hGe) (lixGL_mapsTo hGc hGu hGe)
        (2 * lixRank dd)
      = relPullback (ZMod 2) (lixFarMap hGc hGu) (lixFar_mapsTo hGc hGu)
        (2 * lixRank dd) :=
    RelativeSupport.relPullback_eq_of_homotopy_of_line contractibleSpace_lixI _ _
      (cmap (lixHomotopyFun hGc hGu)) (lixHomotopy_mapsTo hGc hGu)
      (lixHomotopy_end_one hGc hGu hGe) (lixHomotopy_end_zero hGc hGu)
      (lixGL_mapsTo hGc hGu hGe) (lixFar_mapsTo hGc hGu) (2 * lixRank dd)
      (by have := two_le_two_mul_lixRank dd; omega) (lixULine hGc hGu)
  rw [hcut, relPullback_lixFar_eq_lixGR' hGc hGu,
    relPullback_congr_map (lixGRmap_eq hGc hGu).symm (lixGR'_mapsTo hGc hGu)
      (lixGR_mapsTo hGc hGu) (2 * lixRank dd)]

/-! ## 4. The two legs as composites of pullbacks -/

theorem relPullback_lixGL_chain (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) :
    relPullback (ZMod 2) (lixGLmap hGc hGu hGe) (lixGL_mapsTo hGc hGu hGe)
        (2 * lixRank dd)
      = (relPullback (ZMod 2) (lixSecMap hGc hGu hGe) (lixSectionTotal_mapsTo hGc hGu hGe)
            (2 * lixRank dd)
          ≫ relPullback (ZMod 2) (lixIncB dd) (lixIncB_mapsTo dd) (2 * lixRank dd)
          ≫ relPullback (ZMod 2) (lixNbhdMap dd) (lixNbhdMap_mapsTo dd) (2 * lixRank dd))
        ≫ relPullback (ZMod 2) (lixShrinkMap hGc hGu) (lixShrink_mapsTo hGc hGu)
            (2 * lixRank dd) := by
  have hcd : ∀ x ∈ ((Subtype.val : ↥(lixBC dd).target → (↥sphereOne × baseM dd)) ⁻¹'
      ({lixZero dd}ᶜ : Set (↥sphereOne × baseM dd))),
      (ConcreteCategory.hom (lixIncB dd ≫ lixSecMap hGc hGu hGe)) x
        ∈ lixPuncturedInTotal hGc hGu :=
    fun x hx => lixSectionTotal_mapsTo hGc hGu hGe _ (lixIncB_mapsTo dd x hx)
  have hbcd : ∀ x ∈ ((Subtype.val : ↥(lixFC dd).target → (Fin (lixRank dd) → ℂ)) ⁻¹'
      ({(0 : Fin (lixRank dd) → ℂ)}ᶜ)),
      (ConcreteCategory.hom (lixNbhdMap dd ≫ (lixIncB dd ≫ lixSecMap hGc hGu hGe))) x
        ∈ lixPuncturedInTotal hGc hGu :=
    fun x hx => hcd _ (lixNbhdMap_mapsTo dd x hx)
  have s1 : relPullback (ZMod 2) (lixGLmap hGc hGu hGe) (lixGL_mapsTo hGc hGu hGe)
        (2 * lixRank dd)
      = relPullback (ZMod 2) (lixNbhdMap dd ≫ (lixIncB dd ≫ lixSecMap hGc hGu hGe)) hbcd
          (2 * lixRank dd)
        ≫ relPullback (ZMod 2) (lixShrinkMap hGc hGu) (lixShrink_mapsTo hGc hGu)
          (2 * lixRank dd) :=
    relPullback_comp (ZMod 2) (lixShrinkMap hGc hGu)
      (lixNbhdMap dd ≫ (lixIncB dd ≫ lixSecMap hGc hGu hGe)) (lixShrink_mapsTo hGc hGu)
      hbcd (lixGL_mapsTo hGc hGu hGe) (2 * lixRank dd)
  have s2 : relPullback (ZMod 2) (lixNbhdMap dd ≫ (lixIncB dd ≫ lixSecMap hGc hGu hGe))
        hbcd (2 * lixRank dd)
      = relPullback (ZMod 2) (lixIncB dd ≫ lixSecMap hGc hGu hGe) hcd (2 * lixRank dd)
        ≫ relPullback (ZMod 2) (lixNbhdMap dd) (lixNbhdMap_mapsTo dd) (2 * lixRank dd) :=
    relPullback_comp (ZMod 2) (lixNbhdMap dd) (lixIncB dd ≫ lixSecMap hGc hGu hGe)
      (lixNbhdMap_mapsTo dd) hcd hbcd (2 * lixRank dd)
  have s3 : relPullback (ZMod 2) (lixIncB dd ≫ lixSecMap hGc hGu hGe) hcd
        (2 * lixRank dd)
      = relPullback (ZMod 2) (lixSecMap hGc hGu hGe) (lixSectionTotal_mapsTo hGc hGu hGe)
          (2 * lixRank dd)
        ≫ relPullback (ZMod 2) (lixIncB dd) (lixIncB_mapsTo dd) (2 * lixRank dd) :=
    relPullback_comp (ZMod 2) (lixIncB dd) (lixSecMap hGc hGu hGe) (lixIncB_mapsTo dd)
      (lixSectionTotal_mapsTo hGc hGu hGe) hcd (2 * lixRank dd)
  rw [s1, s2, s3]
  simp only [Category.assoc]

theorem relPullback_lixGR_chain (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    relPullback (ZMod 2) (lixGRmap hGc hGu) (lixGR_mapsTo hGc hGu) (2 * lixRank dd)
      = (relPullback (ZMod 2) (lixInclOn hGc hGu) (lixTotalInclOn_mapsTo hGc hGu)
            (2 * lixRank dd)
          ≫ relPullback (ZMod 2) (lixTrivInv hGc hGu) (lixTrivInv_mapsTo hGc hGu)
            (2 * lixRank dd)
          ≫ relPullback (ZMod 2)
            (RelativeSupport.sliceMap (lixZeroInBall hGc hGu) (Fin (lixRank dd) → ℂ))
            (RelativeSupport.slice_mapsTo (lixZeroInBall hGc hGu)
              (puncturedSet (lixRank dd))) (2 * lixRank dd)
          ≫ relPullback (ZMod 2) (lixIncF dd) (lixIncF_mapsTo dd) (2 * lixRank dd))
        ≫ relPullback (ZMod 2) (lixShrinkMap hGc hGu) (lixShrink_mapsTo hGc hGu)
            (2 * lixRank dd) := by
  have hti : ∀ q ∈ {q : ↥(lixTrivBall hGc hGu) × (Fin (lixRank dd) → ℂ) | q.2 ≠ 0},
      (ConcreteCategory.hom (lixTrivInv hGc hGu ≫ lixInclOn hGc hGu)) q
        ∈ lixPuncturedInTotal hGc hGu :=
    fun q hq => lixTotalInclOn_mapsTo hGc hGu _ (lixTrivInv_mapsTo hGc hGu q hq)
  have hsti : ∀ y ∈ puncturedSet (lixRank dd),
      (ConcreteCategory.hom (RelativeSupport.sliceMap (lixZeroInBall hGc hGu)
        (Fin (lixRank dd) → ℂ) ≫ (lixTrivInv hGc hGu ≫ lixInclOn hGc hGu))) y
        ∈ lixPuncturedInTotal hGc hGu :=
    fun y hy => hti _ (RelativeSupport.slice_mapsTo (lixZeroInBall hGc hGu)
      (puncturedSet (lixRank dd)) y hy)
  have hfsti : ∀ x ∈ ((Subtype.val : ↥(lixFC dd).target → (Fin (lixRank dd) → ℂ)) ⁻¹'
      ({(0 : Fin (lixRank dd) → ℂ)}ᶜ)),
      (ConcreteCategory.hom (lixIncF dd ≫ (RelativeSupport.sliceMap (lixZeroInBall hGc hGu)
        (Fin (lixRank dd) → ℂ) ≫ (lixTrivInv hGc hGu ≫ lixInclOn hGc hGu)))) x
        ∈ lixPuncturedInTotal hGc hGu :=
    fun x hx => hsti _ (lixIncF_mapsTo dd x hx)
  have s1 : relPullback (ZMod 2) (lixGRmap hGc hGu) (lixGR_mapsTo hGc hGu)
        (2 * lixRank dd)
      = relPullback (ZMod 2) (lixIncF dd ≫ (RelativeSupport.sliceMap
          (lixZeroInBall hGc hGu) (Fin (lixRank dd) → ℂ) ≫
          (lixTrivInv hGc hGu ≫ lixInclOn hGc hGu))) hfsti (2 * lixRank dd)
        ≫ relPullback (ZMod 2) (lixShrinkMap hGc hGu) (lixShrink_mapsTo hGc hGu)
          (2 * lixRank dd) :=
    relPullback_comp (ZMod 2) (lixShrinkMap hGc hGu) _ (lixShrink_mapsTo hGc hGu) hfsti
      (lixGR_mapsTo hGc hGu) (2 * lixRank dd)
  have s2 : relPullback (ZMod 2) (lixIncF dd ≫ (RelativeSupport.sliceMap
        (lixZeroInBall hGc hGu) (Fin (lixRank dd) → ℂ) ≫
        (lixTrivInv hGc hGu ≫ lixInclOn hGc hGu))) hfsti (2 * lixRank dd)
      = relPullback (ZMod 2) (RelativeSupport.sliceMap (lixZeroInBall hGc hGu)
          (Fin (lixRank dd) → ℂ) ≫ (lixTrivInv hGc hGu ≫ lixInclOn hGc hGu)) hsti
          (2 * lixRank dd)
        ≫ relPullback (ZMod 2) (lixIncF dd) (lixIncF_mapsTo dd) (2 * lixRank dd) :=
    relPullback_comp (ZMod 2) (lixIncF dd) _ (lixIncF_mapsTo dd) hsti hfsti
      (2 * lixRank dd)
  have s3 : relPullback (ZMod 2) (RelativeSupport.sliceMap (lixZeroInBall hGc hGu)
        (Fin (lixRank dd) → ℂ) ≫ (lixTrivInv hGc hGu ≫ lixInclOn hGc hGu)) hsti
        (2 * lixRank dd)
      = relPullback (ZMod 2) (lixTrivInv hGc hGu ≫ lixInclOn hGc hGu) hti
          (2 * lixRank dd)
        ≫ relPullback (ZMod 2)
          (RelativeSupport.sliceMap (lixZeroInBall hGc hGu) (Fin (lixRank dd) → ℂ))
          (RelativeSupport.slice_mapsTo (lixZeroInBall hGc hGu)
            (puncturedSet (lixRank dd))) (2 * lixRank dd) :=
    relPullback_comp (ZMod 2)
      (RelativeSupport.sliceMap (lixZeroInBall hGc hGu) (Fin (lixRank dd) → ℂ)) _
      (RelativeSupport.slice_mapsTo (lixZeroInBall hGc hGu) (puncturedSet (lixRank dd)))
      hti hsti (2 * lixRank dd)
  have s4 : relPullback (ZMod 2) (lixTrivInv hGc hGu ≫ lixInclOn hGc hGu) hti
        (2 * lixRank dd)
      = relPullback (ZMod 2) (lixInclOn hGc hGu) (lixTotalInclOn_mapsTo hGc hGu)
          (2 * lixRank dd)
        ≫ relPullback (ZMod 2) (lixTrivInv hGc hGu) (lixTrivInv_mapsTo hGc hGu)
          (2 * lixRank dd) :=
    relPullback_comp (ZMod 2) (lixTrivInv hGc hGu) (lixInclOn hGc hGu)
      (lixTrivInv_mapsTo hGc hGu) (lixTotalInclOn_mapsTo hGc hGu) hti (2 * lixRank dd)
  rw [s1, s2, s3, s4]
  simp only [Category.assoc]

/-! ## 5. The square -/

/-- The square after the excision has been composed on and the restriction to `lixU`
has been cancelled. -/
theorem lixHsq_shrunk (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) :
    lixSRel hGc hGu hGe (2 * lixRank dd) ≫ (lixExcB dd).hom ≫ (lixNbhdIso dd).hom
      = lixRes hGc hGu (2 * lixRank dd) ≫ (lixBundlePairIso hGc hGu (2 * lixRank dd)).hom
          ≫ (lixProdIso hGc hGu).hom ≫ (lixExcF dd).hom := by
  have hEq := relPullback_lixGL_eq_lixGR hGc hGu hGe
  rw [relPullback_lixGL_chain hGc hGu hGe, relPullback_lixGR_chain hGc hGu] at hEq
  rw [lixSRel_eq, lixExcB_hom_eq, lixNbhdIso_hom_eq, lixRes_eq, lixBundlePairIso_hom_eq,
    lixProdIso_hom_eq, lixExcF_hom_eq]
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun a => ?_
  refine injective_lixShrink hGc hGu ?_
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, hEq]

/-- **The compatibility square**, at the `hsq` binder of `lix_topClass_ne_zero_of_thom`. -/
theorem lixHsq (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) :
    lixSRel hGc hGu hGe (2 * lixRank dd) ≫ (lixRelModelIso dd (2 * lixRank dd)).hom
      = lixRes hGc hGu (2 * lixRank dd) ≫ (lixLocalPairIsoClosed hGc hGu).hom := by
  have h := lixHsq_shrunk hGc hGu hGe
  rw [lixRelModelIso_hom_eq, lixLocalPairIsoClosed_hom_eq]
  have hassoc : lixSRel hGc hGu hGe (2 * lixRank dd)
        ≫ ((lixExcB dd).hom ≫ (lixNbhdIso dd).hom ≫ (lixExcF dd).inv)
      = (lixSRel hGc hGu hGe (2 * lixRank dd) ≫ (lixExcB dd).hom ≫ (lixNbhdIso dd).hom)
        ≫ (lixExcF dd).inv := by
    simp only [Category.assoc]
  rw [hassoc, h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-! Printed on every build. -/

#print axioms lixHsq

end GroupApproximation.CharClass
