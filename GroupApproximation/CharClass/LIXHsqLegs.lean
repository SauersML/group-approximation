import GroupApproximation.CharClass.LIXHsqHomotopy
import GroupApproximation.CharClass.LIXRestrictionMap

/-!
# The two legs of the compatibility square, as maps out of `lixU`

Lane `lix-hsq`.

`hsq` compares two composites of relative pullbacks.  This file names the map of spaces each
factor is a pullback along, records the identification as a **separate one-line definitional
lemma for each factor**, and assembles the two legs restricted to `lixU`.

## Why the identifications are stated one at a time

Each of them is `rfl`, and the temptation is to let a single `rw`-and-`rfl` at the end of the
argument discharge all seven at once.  That does not typecheck in practice: the terms carry
`relCohomology`, `HomologicalComplex.homologyMap` and the `asIso` of an excision, and the
resulting `whnf` runs past the heartbeat limit with an error that names the whole theorem and
nothing inside it.  Stated one at a time, each is a small delta-reduction and a failure names
the factor that moved.

## Main definitions

* `lixIncB`, `lixIncF`, `lixNbhdMap`, `lixSecMap`, `lixTrivInv`, `lixInclOn` — the six maps.
* `lixGLmap`, `lixGRmap` — **the two legs**; `lixGRmap'` and `lixFarMap` the two forms the
  comparison passes through.

## Main results

* `lixSRel_eq`, `lixExcB_hom_eq`, `lixNbhdIso_hom_eq`, `lixExcF_hom_eq`, `lixRes_eq`,
  `lixBundlePairIso_hom_eq`, `lixProdIso_hom_eq` — the seven identifications.
* `lixGRmap_eq` — the right leg **is** the fibre over the section's zero: the intertwiner at
  the point itself is the identity.
* `lixHomotopy_end_one`, `lixHomotopy_end_zero` — the homotopy's ends are the two legs.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open Set CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-! ## 1. The three isomorphisms inside `lixRelModelIso` -/

/-- Excision at the section's zero, onto the base chart's target. -/
abbrev lixExcB (dd : Fin ℓ → ℕ) :
    relCohomology (ZMod 2) (lixN dd) ({lixZero dd}ᶜ : Set (↥sphereOne × baseM dd))
        (2 * lixRank dd)
      ≅ relCohomology (ZMod 2) (TopCat.of ↥(lixBC dd).target)
        ((Subtype.val : ↥(lixBC dd).target → (↥sphereOne × baseM dd)) ⁻¹'
          ({lixZero dd}ᶜ : Set (↥sphereOne × baseM dd))) (2 * lixRank dd) :=
  excisionIsoPoint (lixN dd) (lixZero dd) ((lixBC dd).target) (lixBC dd).open_target
    lixZero_mem_lixBC_target (2 * lixRank dd)

/-- Excision at the origin, onto the section chart's target. -/
abbrev lixExcF (dd : Fin ℓ → ℕ) :
    relCohomology (ZMod 2) (TopCat.of (Fin (lixRank dd) → ℂ))
        ({(0 : Fin (lixRank dd) → ℂ)}ᶜ) (2 * lixRank dd)
      ≅ relCohomology (ZMod 2) (TopCat.of ↥(lixFC dd).target)
        ((Subtype.val : ↥(lixFC dd).target → (Fin (lixRank dd) → ℂ)) ⁻¹'
          ({(0 : Fin (lixRank dd) → ℂ)}ᶜ)) (2 * lixRank dd) :=
  excisionIsoPoint (TopCat.of (Fin (lixRank dd) → ℂ)) 0 ((lixFC dd).target)
    (lixFC dd).open_target zero_mem_lixFC_target (2 * lixRank dd)

/-- The chart, as an isomorphism of the two punctured neighbourhoods. -/
abbrev lixNbhdIso (dd : Fin ℓ → ℕ) :
    relCohomology (ZMod 2) (TopCat.of ↥(lixBC dd).target)
        ((Subtype.val : ↥(lixBC dd).target → (↥sphereOne × baseM dd)) ⁻¹'
          ({lixZero dd}ᶜ : Set (↥sphereOne × baseM dd))) (2 * lixRank dd)
      ≅ relCohomology (ZMod 2) (TopCat.of ↥(lixFC dd).target)
        ((Subtype.val : ↥(lixFC dd).target → (Fin (lixRank dd) → ℂ)) ⁻¹'
          ({(0 : Fin (lixRank dd) → ℂ)}ᶜ)) (2 * lixRank dd) :=
  relCohomologyCongrPoint (lixNbhdHomeo dd) lixZero_mem_lixBC_target zero_mem_lixFC_target
    lixNbhdHomeo_zero (2 * lixRank dd)

/-- The product-pair identification, at the degree the square runs in. -/
abbrev lixProdIso (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    relCohomology (ZMod 2) (TopCat.of (↥(lixTrivBall hGc hGu) × (Fin (lixRank dd) → ℂ)))
        {q : ↥(lixTrivBall hGc hGu) × (Fin (lixRank dd) → ℂ) | q.2 ≠ 0} (2 * lixRank dd)
      ≅ relCohomology (ZMod 2) (TopCat.of (Fin (lixRank dd) → ℂ))
        (puncturedSet (lixRank dd)) (2 * lixRank dd) :=
  RelativeSupport.relCohomologyProdIso (contractibleSpace_lixTrivBall hGc hGu)
    (lixZeroInBall hGc hGu) (lixRank dd) (2 * lixRank dd) (two_le_two_mul_lixRank dd)

/-! ## 2. The six maps of spaces -/

/-- The inclusion of the base chart's target. -/
def lixIncB (dd : Fin ℓ → ℕ) : TopCat.of ↥(lixBC dd).target ⟶ lixN dd :=
  sInclusion (X := lixN dd) ((lixBC dd).target)

/-- The inclusion of the section chart's target. -/
def lixIncF (dd : Fin ℓ → ℕ) :
    TopCat.of ↥(lixFC dd).target ⟶ TopCat.of (Fin (lixRank dd) → ℂ) :=
  sInclusion (X := TopCat.of (Fin (lixRank dd) → ℂ)) ((lixFC dd).target)

/-- The chart between the two neighbourhoods. -/
def lixNbhdMap (dd : Fin ℓ → ℕ) :
    TopCat.of ↥(lixFC dd).target ⟶ TopCat.of ↥(lixBC dd).target :=
  (TopCat.isoOfHomeo (lixNbhdHomeo dd)).inv

/-- The section, as a morphism of spaces. -/
def lixSecMap (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) :
    lixN dd ⟶ lixTotalPair hGc hGu :=
  cmap (lixSectionTotal hGc hGu hGe)

/-- The trivialisation's inverse, as a morphism of spaces. -/
def lixTrivInv (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    TopCat.of (↥(lixTrivBall hGc hGu) × (Fin (lixRank dd) → ℂ)) ⟶
      TopCat.of (Bundle.Total ((lixBundle G hGc hGu).restrictTo (lixTrivBall hGc hGu))) :=
  (TopCat.isoOfHomeo (Bundle.totalTrivStdOn (lixBundle G hGc hGu) (lixZero dd)
    (lixTrivBall hGc hGu) (lixTrivBall_subset hGc hGu) (lixRank dd)
    (rank_lixBundle G hGc hGu _))).inv

/-- The inclusion of the restricted total space. -/
def lixInclOn (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    TopCat.of (Bundle.Total ((lixBundle G hGc hGu).restrictTo (lixTrivBall hGc hGu))) ⟶
      lixTotalPair hGc hGu :=
  cmap (Bundle.totalInclOn (lixBundle G hGc hGu) (lixTrivBall hGc hGu))

/-! ## 3. Their map-of-pairs hypotheses -/

theorem lixIncB_mapsTo (dd : Fin ℓ → ℕ) :
    ∀ x ∈ ((Subtype.val : ↥(lixBC dd).target → (↥sphereOne × baseM dd)) ⁻¹'
        ({lixZero dd}ᶜ : Set (↥sphereOne × baseM dd))),
      (ConcreteCategory.hom (lixIncB dd)) x
        ∈ ({lixZero dd}ᶜ : Set (↥sphereOne × baseM dd)) :=
  fun _ hx => hx

theorem lixIncF_mapsTo (dd : Fin ℓ → ℕ) :
    ∀ x ∈ ((Subtype.val : ↥(lixFC dd).target → (Fin (lixRank dd) → ℂ)) ⁻¹'
        ({(0 : Fin (lixRank dd) → ℂ)}ᶜ)),
      (ConcreteCategory.hom (lixIncF dd)) x ∈ puncturedSet (lixRank dd) :=
  fun _ hx => hx

theorem lixNbhdMap_mapsTo (dd : Fin ℓ → ℕ) :
    ∀ x ∈ ((Subtype.val : ↥(lixFC dd).target → (Fin (lixRank dd) → ℂ)) ⁻¹'
        ({(0 : Fin (lixRank dd) → ℂ)}ᶜ)),
      (ConcreteCategory.hom (lixNbhdMap dd)) x ∈
        ((Subtype.val : ↥(lixBC dd).target → (↥sphereOne × baseM dd)) ⁻¹'
          ({lixZero dd}ᶜ : Set (↥sphereOne × baseM dd))) := by
  intro x hx hcon
  refine hx ?_
  have h1 : (lixNbhdHomeo dd).symm x = ⟨lixZero dd, lixZero_mem_lixBC_target⟩ :=
    Subtype.ext hcon
  have h2 : x = lixNbhdHomeo dd ⟨lixZero dd, lixZero_mem_lixBC_target⟩ := by
    rw [← h1, (lixNbhdHomeo dd).apply_symm_apply]
  rw [h2, lixNbhdHomeo_zero]
  rfl

theorem lixTrivInv_mapsTo (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    ∀ q ∈ {q : ↥(lixTrivBall hGc hGu) × (Fin (lixRank dd) → ℂ) | q.2 ≠ 0},
      (ConcreteCategory.hom (lixTrivInv hGc hGu)) q ∈
        {w : Bundle.Total ((lixBundle G hGc hGu).restrictTo (lixTrivBall hGc hGu)) |
          (w : ↥(lixTrivBall hGc hGu) × (VIdx dd ⊕ VIdx dd → ℂ))
            ∈ Bundle.puncturedSet
              ((lixBundle G hGc hGu).restrictTo (lixTrivBall hGc hGu))} := by
  intro q hq
  refine ⟨((Bundle.totalTrivStdOn (lixBundle G hGc hGu) (lixZero dd) (lixTrivBall hGc hGu)
    (lixTrivBall_subset hGc hGu) (lixRank dd) (rank_lixBundle G hGc hGu _)).symm q).2, ?_⟩
  intro hzero
  refine hq ?_
  have h := (Bundle.totalTrivStdOn_snd_eq_zero_iff (lixBundle G hGc hGu) (lixZero dd)
    (lixTrivBall hGc hGu) (lixTrivBall_subset hGc hGu) (lixRank dd)
    (rank_lixBundle G hGc hGu _)
    ((Bundle.totalTrivStdOn (lixBundle G hGc hGu) (lixZero dd) (lixTrivBall hGc hGu)
      (lixTrivBall_subset hGc hGu) (lixRank dd) (rank_lixBundle G hGc hGu _)).symm q)).mpr
    hzero
  rwa [Homeomorph.apply_symm_apply] at h

/-! ## 4. The seven identifications, one at a time -/

theorem lixSRel_eq (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) :
    lixSRel hGc hGu hGe (2 * lixRank dd)
      = relPullback (ZMod 2) (lixSecMap hGc hGu hGe) (lixSectionTotal_mapsTo hGc hGu hGe)
        (2 * lixRank dd) := rfl

theorem lixExcB_hom_eq (dd : Fin ℓ → ℕ) :
    (lixExcB dd).hom
      = relPullback (ZMod 2) (lixIncB dd) (lixIncB_mapsTo dd) (2 * lixRank dd) := rfl

theorem lixNbhdIso_hom_eq (dd : Fin ℓ → ℕ) :
    (lixNbhdIso dd).hom
      = relPullback (ZMod 2) (lixNbhdMap dd) (lixNbhdMap_mapsTo dd) (2 * lixRank dd) := rfl

theorem lixExcF_hom_eq (dd : Fin ℓ → ℕ) :
    (lixExcF dd).hom
      = relPullback (ZMod 2) (lixIncF dd) (lixIncF_mapsTo dd) (2 * lixRank dd) := rfl

theorem lixRes_eq (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    lixRes hGc hGu (2 * lixRank dd)
      = relPullback (ZMod 2) (lixInclOn hGc hGu) (lixTotalInclOn_mapsTo hGc hGu)
        (2 * lixRank dd) := rfl

theorem lixBundlePairIso_hom_eq (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    (lixBundlePairIso hGc hGu (2 * lixRank dd)).hom
      = relPullback (ZMod 2) (lixTrivInv hGc hGu) (lixTrivInv_mapsTo hGc hGu)
        (2 * lixRank dd) := rfl

theorem lixProdIso_hom_eq (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    (lixProdIso hGc hGu).hom
      = relPullback (ZMod 2)
        (RelativeSupport.sliceMap (lixZeroInBall hGc hGu) (Fin (lixRank dd) → ℂ))
        (RelativeSupport.slice_mapsTo (lixZeroInBall hGc hGu) (puncturedSet (lixRank dd)))
        (2 * lixRank dd) := rfl

theorem lixLocalPairIsoClosed_hom_eq (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    (lixLocalPairIsoClosed hGc hGu).hom
      = (lixBundlePairIso hGc hGu (2 * lixRank dd)).hom ≫ (lixProdIso hGc hGu).hom := rfl

theorem lixRelModelIso_hom_eq (dd : Fin ℓ → ℕ) :
    (lixRelModelIso dd (2 * lixRank dd)).hom
      = (lixExcB dd).hom ≫ (lixNbhdIso dd).hom ≫ (lixExcF dd).inv := rfl

/-! ## 5. The two legs -/

/-- The left leg's map: the section at the chart point. -/
def lixGLmap (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) :
    TopCat.of ↥(lixU hGc hGu) ⟶ lixTotalPair hGc hGu :=
  lixShrinkMap hGc hGu ≫ (lixNbhdMap dd ≫ (lixIncB dd ≫ lixSecMap hGc hGu hGe))

/-- The right leg's map. -/
def lixGRmap (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    TopCat.of ↥(lixU hGc hGu) ⟶ lixTotalPair hGc hGu :=
  lixShrinkMap hGc hGu ≫ (lixIncF dd ≫
    (RelativeSupport.sliceMap (lixZeroInBall hGc hGu) (Fin (lixRank dd) → ℂ) ≫
      (lixTrivInv hGc hGu ≫ lixInclOn hGc hGu)))

/-- The right leg without the trivialisation, which is what it computes to. -/
def lixGRmap' (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    TopCat.of ↥(lixU hGc hGu) ⟶ lixTotalPair hGc hGu :=
  (lixShrinkMap hGc hGu ≫ lixIncF dd) ≫ cmap (lixFibreMap hGc hGu)

/-- The far end of the homotopy: the right leg precomposed with the linear automorphism. -/
def lixFarMap (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    TopCat.of ↥(lixU hGc hGu) ⟶ lixTotalPair hGc hGu :=
  (lixShrinkMap hGc hGu ≫ lixIncF dd) ≫ (lixKMap hGc hGu ≫ cmap (lixFibreMap hGc hGu))

theorem lixSplit_mapsTo (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    ∀ x ∈ ((Subtype.val : ↥(lixU hGc hGu) → (Fin (lixRank dd) → ℂ)) ⁻¹'
        ({(0 : Fin (lixRank dd) → ℂ)}ᶜ)),
      (ConcreteCategory.hom (lixShrinkMap hGc hGu ≫ lixIncF dd)) x
        ∈ puncturedSet (lixRank dd) :=
  fun x hx => lixIncF_mapsTo dd _ (lixShrink_mapsTo hGc hGu x hx)

theorem lixFibreMap_mapsTo (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    ∀ y ∈ puncturedSet (lixRank dd),
      (ConcreteCategory.hom (cmap (lixFibreMap hGc hGu))) y
        ∈ lixPuncturedInTotal hGc hGu := by
  intro y hy
  refine ⟨lixFibre_mem hGc hGu y, ?_⟩
  intro hzero
  refine hy ?_
  have h2 : (lixFrame hGc hGu)ᴴ *ᵥ (lixFrame hGc hGu *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, lixFrame_conjTranspose_mul, Matrix.one_mulVec]
  have h3 : lixFrame hGc hGu *ᵥ y = 0 := hzero
  rw [h3, Matrix.mulVec_zero] at h2
  exact h2.symm

theorem lixKFibre_mapsTo (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    ∀ y ∈ puncturedSet (lixRank dd),
      (ConcreteCategory.hom (lixKMap hGc hGu ≫ cmap (lixFibreMap hGc hGu))) y
        ∈ lixPuncturedInTotal hGc hGu :=
  fun y hy => lixFibreMap_mapsTo hGc hGu _ (lixKHomeo_mapsTo hGc hGu y hy)

theorem lixGL_mapsTo (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) :
    ∀ x ∈ ((Subtype.val : ↥(lixU hGc hGu) → (Fin (lixRank dd) → ℂ)) ⁻¹'
        ({(0 : Fin (lixRank dd) → ℂ)}ᶜ)),
      (ConcreteCategory.hom (lixGLmap hGc hGu hGe)) x ∈ lixPuncturedInTotal hGc hGu :=
  fun x hx =>
    lixSectionTotal_mapsTo hGc hGu hGe _
      (lixIncB_mapsTo dd _ (lixNbhdMap_mapsTo dd _ (lixShrink_mapsTo hGc hGu x hx)))

theorem lixGR_mapsTo (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    ∀ x ∈ ((Subtype.val : ↥(lixU hGc hGu) → (Fin (lixRank dd) → ℂ)) ⁻¹'
        ({(0 : Fin (lixRank dd) → ℂ)}ᶜ)),
      (ConcreteCategory.hom (lixGRmap hGc hGu)) x ∈ lixPuncturedInTotal hGc hGu :=
  fun x hx =>
    lixTotalInclOn_mapsTo hGc hGu _
      (lixTrivInv_mapsTo hGc hGu _
        (RelativeSupport.slice_mapsTo (lixZeroInBall hGc hGu) (puncturedSet (lixRank dd)) _
          (lixIncF_mapsTo dd _ (lixShrink_mapsTo hGc hGu x hx))))

theorem lixGR'_mapsTo (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    ∀ x ∈ ((Subtype.val : ↥(lixU hGc hGu) → (Fin (lixRank dd) → ℂ)) ⁻¹'
        ({(0 : Fin (lixRank dd) → ℂ)}ᶜ)),
      (ConcreteCategory.hom (lixGRmap' hGc hGu)) x ∈ lixPuncturedInTotal hGc hGu :=
  fun x hx => lixFibreMap_mapsTo hGc hGu _ (lixSplit_mapsTo hGc hGu x hx)

theorem lixFar_mapsTo (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    ∀ x ∈ ((Subtype.val : ↥(lixU hGc hGu) → (Fin (lixRank dd) → ℂ)) ⁻¹'
        ({(0 : Fin (lixRank dd) → ℂ)}ᶜ)),
      (ConcreteCategory.hom (lixFarMap hGc hGu)) x ∈ lixPuncturedInTotal hGc hGu :=
  fun x hx => lixKFibre_mapsTo hGc hGu _ (lixSplit_mapsTo hGc hGu x hx)

/-! ## 6. The right leg computes to the fibre map -/

/-- **The trivialisation's inverse over the section's zero is the frame.**  Proved forward,
through `Homeomorph.symm_apply_eq`: reducing the inverse itself runs past the heartbeat
limit, while the forward map is three structure projections. -/
theorem lixTrivInv_apply (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) (y : Fin (lixRank dd) → ℂ) :
    (ConcreteCategory.hom (lixTrivInv hGc hGu)) (lixZeroInBall hGc hGu, y)
      = ⟨(lixZeroInBall hGc hGu, lixFrame hGc hGu *ᵥ y), lixFibre_mem hGc hGu y⟩ := by
  refine (Homeomorph.symm_apply_eq _).mpr ?_
  refine Prod.ext rfl ?_
  show y = (lixFrame hGc hGu)ᴴ *ᵥ
    (Bundle.intert (lixBundle G hGc hGu) (lixZero dd) (lixZero dd)
      *ᵥ (lixFrame hGc hGu *ᵥ y))
  rw [Bundle.intert_self, Matrix.one_mulVec, Matrix.mulVec_mulVec,
    lixFrame_conjTranspose_mul, Matrix.one_mulVec]

theorem lixGRmap_eq (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    lixGRmap hGc hGu = lixGRmap' hGc hGu := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro v
  show (ConcreteCategory.hom (lixInclOn hGc hGu))
      ((ConcreteCategory.hom (lixTrivInv hGc hGu))
        (lixZeroInBall hGc hGu, (v : Fin (lixRank dd) → ℂ)))
    = lixFibreMap hGc hGu (v : Fin (lixRank dd) → ℂ)
  rw [lixTrivInv_apply hGc hGu]
  rfl

/-! ## 7. The homotopy's two ends -/

theorem lixNbhdMap_val (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) (v : ↥(lixU hGc hGu)) :
    (((ConcreteCategory.hom (lixNbhdMap dd))
        ((ConcreteCategory.hom (lixShrinkMap hGc hGu)) v) : ↥(lixBC dd).target) :
        ↥sphereOne × baseM dd) = lixBaseChartFun dd (lixQ hGc hGu v) := rfl

theorem lixGLmap_apply (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) (v : ↥(lixU hGc hGu)) :
    (ConcreteCategory.hom (lixGLmap hGc hGu hGe)) v
      = lixSectionTotal hGc hGu hGe (lixBaseChartFun dd (lixQ hGc hGu v)) := by
  show lixSectionTotal hGc hGu hGe
    (((ConcreteCategory.hom (lixNbhdMap dd))
      ((ConcreteCategory.hom (lixShrinkMap hGc hGu)) v) : ↥(lixBC dd).target) :
      ↥sphereOne × baseM dd) = _
  rw [lixNbhdMap_val]

theorem lixFarMap_apply (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (v : ↥(lixU hGc hGu)) :
    (ConcreteCategory.hom (lixFarMap hGc hGu)) v
      = lixFibreMap hGc hGu (lixKLin hGc hGu (v : Fin (lixRank dd) → ℂ)) := rfl

theorem lixHomotopy_end_one (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) :
    RelativeSupport.sliceMap (⟨(1 : ℝ), Set.right_mem_Icc.mpr zero_le_one⟩ : ↥lixI)
        (↥(lixU hGc hGu)) ≫ cmap (lixHomotopyFun hGc hGu)
      = lixGLmap hGc hGu hGe := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro v
  exact (lixHomotopy_at_one hGc hGu hGe v).trans (lixGLmap_apply hGc hGu hGe v).symm

theorem lixHomotopy_end_zero (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    RelativeSupport.sliceMap (⟨(0 : ℝ), Set.left_mem_Icc.mpr zero_le_one⟩ : ↥lixI)
        (↥(lixU hGc hGu)) ≫ cmap (lixHomotopyFun hGc hGu)
      = lixFarMap hGc hGu := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro v
  exact (lixHomotopy_at_zero hGc hGu v).trans (lixFarMap_apply hGc hGu v).symm

/-! Printed on every build. -/

#print axioms lixGRmap_eq

end GroupApproximation.CharClass
