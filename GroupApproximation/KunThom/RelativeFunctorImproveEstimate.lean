import GroupApproximation.KunThom.RelativeFunctorImproveFrame

/-!
# Estimate (7) for the relative cluster functor over a cluster frame

`CountingEndgame.CompressorRelativeData` carries, for its distinguished compressor, estimate
(7) of Kun--Thom, arXiv:2608.06222v3, Lemma 4.3: every representative `θ` of the image of
the class of a representative `c` lies within an error of the transport of `c` through the
bridges realized by `A(t)⁻¹`, and the error is at most three times the scale of the image
object.  This file proves both for `RelativeFunctorImprove.frameRelativeFunctor`.

* `frameEstimateError F n π hsurj X Z`: the pair radius of the images of `X` and `Z` plus the
  improvement radius `improveRadius` of the pair.
* `frameRelativeFunctor_estimate`: estimate (7), through
  `GroupoidPresentation.ClusterMetric.twoSidedDisagreement_sandwich_lt_of_ofRep_eq` for the
  assembled functor.  The inputs of that lemma are rebuilt from the hypotheses of
  `frameRelativeFunctor`.
* `frameEstimateError_le`: the error is at most three times the scale of the image of `X`.
  The pair radius is at most twice that scale, and the improvement radius is at most a
  hundredth of the scale of `X`, which is within `11 / 10` of the scale of its image.
* `frameRelativeFunctorOfGood_estimate` and `frameEstimateError_le_of_good`: the same for
  `frameRelativeFunctorOfGood`.
-/

namespace GroupApproximation
namespace RelativeFunctorImprove

open CategoryTheory GroupoidPresentation CompressorNormalizationAssembly BlockPatching
open Classical

/-- The error of estimate (7) at a pair of retained objects: the pair radius of their images
plus the improvement radius of the pair. -/
noncomputable def frameEstimateError {G : Type} [Group G] {A : SoficApproximation G}
    {K : Type} [Group K] {ι : K →* G} {R : RetainedComponents A K ι} (F : ClusterFrame R)
    (n : ℕ) {matched retained : Finset (F.Obj n)} (π : F.Obj n → F.Obj n)
    (hsurj : Set.SurjOn π (matched : Set (F.Obj n)) (retained : Set (F.Obj n)))
    (X Z : ((F.system n).presentation.restrict (retained : Set (F.Obj n))).Obj) : ℕ :=
  (F.system n).clusterMetric.radius (ClusterMetric.matchingInverse π hsurj X.val).1
      (ClusterMetric.matchingInverse π hsurj Z.val).1 +
    improveRadius (F.system n) (ClusterMetric.matchingInverse π hsurj) X.val Z.val

/-- **Estimate (7) for `frameRelativeFunctor`.**  Every representative of the image of the
class of `c` lies within `frameEstimateError` of the transport of `c` through the bridges
realized by `A(q)⁻¹`. -/
theorem frameRelativeFunctor_estimate {G : Type} [Group G] {A : SoficApproximation G}
    {K : Type} [Group K] {ι : K →* G} {R : RetainedComponents A K ι} (F : ClusterFrame R)
    (n : ℕ) (q : G) (ws : ↥R.data.generators → List ↥R.data.generators) {k : ℕ}
    (hk : ∀ s, (ws s).length ≤ k)
    (hK₀ : 2 * (1 + (Fintype.card ↥R.data.generators : ℝ) * k) ≤ F.repairFactor)
    (matched retained : Finset (F.Obj n)) (π : F.Obj n → F.Obj n)
    (hmaps : Set.MapsTo π (matched : Set (F.Obj n)) (retained : Set (F.Obj n)))
    (hinj : Set.InjOn π (matched : Set (F.Obj n)))
    (hsurj : Set.SurjOn π (matched : Set (F.Obj n)) (retained : Set (F.Obj n)))
    (hbridge : ∀ i ∈ matched,
      100 * (((F.embedding n).bridge (A.map n q) i (π i)).sourceDefect +
        ((F.embedding n).bridge (A.map n q) i (π i)).targetDefect) ≤ (F.system n).scale (π i))
    (herr : ∀ i ∈ matched,
      40 * ((inError (F.embedding n) (F.action n) (A.map n q)⁻¹ ws (π i) i +
        outError (F.embedding n) (F.action n) (A.map n q)⁻¹ ws (π i) i : ℕ) : ℝ) ≤
        F.threshold n * (F.system n).scale (π i))
    (hscale : ∀ i ∈ matched, 400 ≤ (F.system n).scale (π i))
    {X Z : ((F.system n).presentation.restrict (retained : Set (F.Obj n))).Obj}
    (c : (F.system n).presentation.Rep X.val.1 Z.val.1)
    (θ : (F.system n).presentation.Rep
      ((frameRelativeFunctor F n q ws hk hK₀ matched retained π hmaps hinj hsurj hbridge herr
        hscale).F.toFunctor.obj X).val.1
      ((frameRelativeFunctor F n q ws hk hK₀ matched retained π hmaps hinj hsurj hbridge herr
        hscale).F.toFunctor.obj Z).val.1)
    (hθ : ((F.system n).presentation.restrict (matched : Set (F.Obj n))).ofRep
        (X := (frameRelativeFunctor F n q ws hk hK₀ matched retained π hmaps hinj hsurj hbridge
          herr hscale).F.toFunctor.obj X)
        (Y := (frameRelativeFunctor F n q ws hk hK₀ matched retained π hmaps hinj hsurj hbridge
          herr hscale).F.toFunctor.obj Z) θ =
      (frameRelativeFunctor F n q ws hk hK₀ matched retained π hmaps hinj hsurj hbridge herr
        hscale).F.toFunctor.map
        (((F.system n).presentation.restrict (retained : Set (F.Obj n))).ofRep
          (X := X) (Y := Z) c)) :
    ((F.system n).clusterMetric.val θ).twoSidedDisagreement
      (FinitePartialBijection.sandwich
        ((F.embedding n).bridge (A.map n q)⁻¹ X.val.1
          ((frameRelativeFunctor F n q ws hk hK₀ matched retained π hmaps hinj hsurj hbridge
            herr hscale).F.toFunctor.obj X).val.1)
        ((F.embedding n).bridge (A.map n q)⁻¹ Z.val.1
          ((frameRelativeFunctor F n q ws hk hK₀ matched retained π hmaps hinj hsurj hbridge
            herr hscale).F.toFunctor.obj Z).val.1)
        ((F.system n).clusterMetric.val c)) < frameEstimateError F n π hsurj X Z := by
  have hβ := bridgeMass_le_of_matched F n q hsurj hbridge
  have hobj := hobj_of_bridge (F.system n) (ClusterMetric.matchingInverse π hsurj)
    (fun X ↦ (F.embedding n).bridge (A.map n q)⁻¹ X.1
      (ClusterMetric.matchingInverse π hsurj X).1)
    (fun X ↦ ((F.embedding n).bridge (A.map n q)⁻¹ X.1
        (ClusterMetric.matchingInverse π hsurj X).1).sourceDefect +
      ((F.embedding n).bridge (A.map n q)⁻¹ X.1
        (ClusterMetric.matchingInverse π hsurj X).1).targetDefect)
    (fun _ ↦ le_refl _) hβ
  have hρ := hundred_mul_improveRadius_le (F.system n) (ClusterMetric.matchingInverse π hsurj)
    (F.distance_nonneg n) (F.distance_small n) (scale_le_of_matched F n hsurj hscale) hobj
  have hforward := hforward_of_words (F.system n) (F.embedAt n) (F.embedAt_injective n)
    (F.embedAt_disjoint n) (fun s ↦ A.map n (ι (s : K))) (A.map n q) ws hk hK₀
    (ClusterMetric.matchingInverse π hsurj) hobj (errorMass_le_of_matched F n q ws hsurj herr)
  have hbackward := hbackward_of_words (F.system n) (F.embedAt n) (F.embedAt_injective n)
    (F.embedAt_disjoint n) (fun s ↦ A.map n (ι (s : K))) (A.map n q) ws hk hK₀
    (ClusterMetric.matchingInverse π hsurj) hobj (errorMass_le_of_matched F n q ws hsurj herr)
  have himprove := himprove_of_defects (F.system n) (ClusterMetric.matchingInverse π hsurj)
    (fun X ↦ (F.embedding n).bridge (A.map n q)⁻¹ X.1
      (ClusterMetric.matchingInverse π hsurj X).1)
    (improveRadius (F.system n) (ClusterMetric.matchingInverse π hsurj)) hforward hbackward
    (fun _ _ b ↦ lt_improveRadius (F.system n) (ClusterMetric.matchingInverse π hsurj) b)
  exact ClusterMetric.twoSidedDisagreement_sandwich_lt_of_ofRep_eq (F.system n).clusterMetric
    (F.system n).clusterMetric (ClusterMetric.matchingInverse π hsurj)
    (fun X ↦ (F.embedding n).bridge (A.map n q)⁻¹ X.1
      (ClusterMetric.matchingInverse π hsurj X).1)
    (fun X ↦ ((F.embedding n).bridge (A.map n q)⁻¹ X.1
        (ClusterMetric.matchingInverse π hsurj X).1).sourceDefect +
      ((F.embedding n).bridge (A.map n q)⁻¹ X.1
        (ClusterMetric.matchingInverse π hsurj X).1).targetDefect)
    (improveRadius (F.system n) (ClusterMetric.matchingInverse π hsurj)) (fun _ ↦ le_refl _)
    himprove
    (fun {X Y} f ↦ ScaledPartialClusterSystem.relativeFunctor_respects_of_small (F.system n)
      (ClusterMetric.matchingInverse π hsurj) _
      (improveRadius (F.system n) (ClusterMetric.matchingInverse π hsurj)) hβ hρ hobj
      (X := X) (Y := Y) f)
    (fun {X Y Z} f g ↦ ScaledPartialClusterSystem.relativeFunctor_comp_of_small (F.system n)
      (ClusterMetric.matchingInverse π hsurj) _
      (improveRadius (F.system n) (ClusterMetric.matchingInverse π hsurj)) hβ hρ hobj
      (X := X) (Y := Y) (Z := Z) f g)
    (X := X.val) (Y := Z.val) c θ hθ

/-- **The error of estimate (7) is at most three times the scale of the image.** -/
theorem frameEstimateError_le {G : Type} [Group G] {A : SoficApproximation G}
    {K : Type} [Group K] {ι : K →* G} {R : RetainedComponents A K ι} (F : ClusterFrame R)
    (n : ℕ) (q : G) (ws : ↥R.data.generators → List ↥R.data.generators) {k : ℕ}
    (hk : ∀ s, (ws s).length ≤ k)
    (hK₀ : 2 * (1 + (Fintype.card ↥R.data.generators : ℝ) * k) ≤ F.repairFactor)
    (matched retained : Finset (F.Obj n)) (π : F.Obj n → F.Obj n)
    (hmaps : Set.MapsTo π (matched : Set (F.Obj n)) (retained : Set (F.Obj n)))
    (hinj : Set.InjOn π (matched : Set (F.Obj n)))
    (hsurj : Set.SurjOn π (matched : Set (F.Obj n)) (retained : Set (F.Obj n)))
    (hbridge : ∀ i ∈ matched,
      100 * (((F.embedding n).bridge (A.map n q) i (π i)).sourceDefect +
        ((F.embedding n).bridge (A.map n q) i (π i)).targetDefect) ≤ (F.system n).scale (π i))
    (herr : ∀ i ∈ matched,
      40 * ((inError (F.embedding n) (F.action n) (A.map n q)⁻¹ ws (π i) i +
        outError (F.embedding n) (F.action n) (A.map n q)⁻¹ ws (π i) i : ℕ) : ℝ) ≤
        F.threshold n * (F.system n).scale (π i))
    (hscale : ∀ i ∈ matched, 400 ≤ (F.system n).scale (π i))
    (X Z : ((F.system n).presentation.restrict (retained : Set (F.Obj n))).Obj) :
    frameEstimateError F n π hsurj X Z ≤
      3 * (F.system n).scale
        ((frameRelativeFunctor F n q ws hk hK₀ matched retained π hmaps hinj hsurj hbridge herr
          hscale).F.toFunctor.obj X).val.1 := by
  have hβ := bridgeMass_le_of_matched F n q hsurj hbridge
  have hobj := hobj_of_bridge (F.system n) (ClusterMetric.matchingInverse π hsurj)
    (fun X ↦ (F.embedding n).bridge (A.map n q)⁻¹ X.1
      (ClusterMetric.matchingInverse π hsurj X).1)
    (fun X ↦ ((F.embedding n).bridge (A.map n q)⁻¹ X.1
        (ClusterMetric.matchingInverse π hsurj X).1).sourceDefect +
      ((F.embedding n).bridge (A.map n q)⁻¹ X.1
        (ClusterMetric.matchingInverse π hsurj X).1).targetDefect)
    (fun _ ↦ le_refl _) hβ
  have hρ := hundred_mul_improveRadius_le (F.system n) (ClusterMetric.matchingInverse π hsurj)
    (F.distance_nonneg n) (F.distance_small n) (scale_le_of_matched F n hsurj hscale) hobj
    X.val Z.val
  obtain ⟨hXo, -⟩ := hobj X.val
  have hm := min_le_left ((F.system n).scale (ClusterMetric.matchingInverse π hsurj X.val).1)
    ((F.system n).scale (ClusterMetric.matchingInverse π hsurj Z.val).1)
  have hs := min_le_left ((F.system n).scale X.val.1) ((F.system n).scale Z.val.1)
  show 2 * min ((F.system n).scale (ClusterMetric.matchingInverse π hsurj X.val).1)
      ((F.system n).scale (ClusterMetric.matchingInverse π hsurj Z.val).1) +
    improveRadius (F.system n) (ClusterMetric.matchingInverse π hsurj) X.val Z.val ≤
      3 * (F.system n).scale (ClusterMetric.matchingInverse π hsurj X.val).1
  omega

/-- Estimate (7) for `frameRelativeFunctorOfGood`. -/
theorem frameRelativeFunctorOfGood_estimate {G : Type} [Group G] {A : SoficApproximation G}
    {K : Type} [Group K] {ι : K →* G} {R : RetainedComponents A K ι} (F : ClusterFrame R)
    (n : ℕ) (q : G) (ws : ↥R.data.generators → List ↥R.data.generators) {k : ℕ}
    (hk : ∀ s, (ws s).length ≤ k)
    (hK₀ : 2 * (1 + (Fintype.card ↥R.data.generators : ℝ) * k) ≤ F.repairFactor)
    (domain good : Finset (F.Obj n)) (π : F.Obj n → F.Obj n)
    (hπ : Set.InjOn π (domain : Set (F.Obj n)))
    (hbridge : ∀ i ∈ good,
      100 * (((F.embedding n).bridge (A.map n q) i (π i)).sourceDefect +
        ((F.embedding n).bridge (A.map n q) i (π i)).targetDefect) ≤ (F.system n).scale (π i))
    (herr : ∀ i ∈ good,
      40 * ((inError (F.embedding n) (F.action n) (A.map n q)⁻¹ ws (π i) i +
        outError (F.embedding n) (F.action n) (A.map n q)⁻¹ ws (π i) i : ℕ) : ℝ) ≤
        F.threshold n * (F.system n).scale (π i))
    (hscale : ∀ i ∈ good, 400 ≤ (F.system n).scale (π i))
    {X Z : ((F.system n).presentation.restrict
      (((domain ∩ good).image π : Finset (F.Obj n)) : Set (F.Obj n))).Obj}
    (c : (F.system n).presentation.Rep X.val.1 Z.val.1)
    (θ : (F.system n).presentation.Rep
      ((frameRelativeFunctorOfGood F n q ws hk hK₀ domain good π hπ hbridge herr
        hscale).F.toFunctor.obj X).val.1
      ((frameRelativeFunctorOfGood F n q ws hk hK₀ domain good π hπ hbridge herr
        hscale).F.toFunctor.obj Z).val.1)
    (hθ : ((F.system n).presentation.restrict
        ((domain ∩ good : Finset (F.Obj n)) : Set (F.Obj n))).ofRep
        (X := (frameRelativeFunctorOfGood F n q ws hk hK₀ domain good π hπ hbridge herr
          hscale).F.toFunctor.obj X)
        (Y := (frameRelativeFunctorOfGood F n q ws hk hK₀ domain good π hπ hbridge herr
          hscale).F.toFunctor.obj Z) θ =
      (frameRelativeFunctorOfGood F n q ws hk hK₀ domain good π hπ hbridge herr
        hscale).F.toFunctor.map
        (((F.system n).presentation.restrict
          (((domain ∩ good).image π : Finset (F.Obj n)) : Set (F.Obj n))).ofRep
          (X := X) (Y := Z) c)) :
    ((F.system n).clusterMetric.val θ).twoSidedDisagreement
      (FinitePartialBijection.sandwich
        ((F.embedding n).bridge (A.map n q)⁻¹ X.val.1
          ((frameRelativeFunctorOfGood F n q ws hk hK₀ domain good π hπ hbridge herr
            hscale).F.toFunctor.obj X).val.1)
        ((F.embedding n).bridge (A.map n q)⁻¹ Z.val.1
          ((frameRelativeFunctorOfGood F n q ws hk hK₀ domain good π hπ hbridge herr
            hscale).F.toFunctor.obj Z).val.1)
        ((F.system n).clusterMetric.val c)) <
      frameEstimateError F n π (finsetSurjOn_image π (domain ∩ good)) X Z :=
  frameRelativeFunctor_estimate F n q ws hk hK₀ (domain ∩ good) ((domain ∩ good).image π) π
    (finsetMapsTo_image π (domain ∩ good)) (finsetInjOn_inter good hπ)
    (finsetSurjOn_image π (domain ∩ good))
    (fun i hi ↦ hbridge i (Finset.mem_inter.mp hi).2)
    (fun i hi ↦ herr i (Finset.mem_inter.mp hi).2)
    (fun i hi ↦ hscale i (Finset.mem_inter.mp hi).2) c θ hθ

/-- The error of estimate (7) for `frameRelativeFunctorOfGood` is at most three times the
scale of the image. -/
theorem frameEstimateError_le_of_good {G : Type} [Group G] {A : SoficApproximation G}
    {K : Type} [Group K] {ι : K →* G} {R : RetainedComponents A K ι} (F : ClusterFrame R)
    (n : ℕ) (q : G) (ws : ↥R.data.generators → List ↥R.data.generators) {k : ℕ}
    (hk : ∀ s, (ws s).length ≤ k)
    (hK₀ : 2 * (1 + (Fintype.card ↥R.data.generators : ℝ) * k) ≤ F.repairFactor)
    (domain good : Finset (F.Obj n)) (π : F.Obj n → F.Obj n)
    (hπ : Set.InjOn π (domain : Set (F.Obj n)))
    (hbridge : ∀ i ∈ good,
      100 * (((F.embedding n).bridge (A.map n q) i (π i)).sourceDefect +
        ((F.embedding n).bridge (A.map n q) i (π i)).targetDefect) ≤ (F.system n).scale (π i))
    (herr : ∀ i ∈ good,
      40 * ((inError (F.embedding n) (F.action n) (A.map n q)⁻¹ ws (π i) i +
        outError (F.embedding n) (F.action n) (A.map n q)⁻¹ ws (π i) i : ℕ) : ℝ) ≤
        F.threshold n * (F.system n).scale (π i))
    (hscale : ∀ i ∈ good, 400 ≤ (F.system n).scale (π i))
    (X Z : ((F.system n).presentation.restrict
      (((domain ∩ good).image π : Finset (F.Obj n)) : Set (F.Obj n))).Obj) :
    frameEstimateError F n π (finsetSurjOn_image π (domain ∩ good)) X Z ≤
      3 * (F.system n).scale
        ((frameRelativeFunctorOfGood F n q ws hk hK₀ domain good π hπ hbridge herr
          hscale).F.toFunctor.obj X).val.1 :=
  frameEstimateError_le F n q ws hk hK₀ (domain ∩ good) ((domain ∩ good).image π) π
    (finsetMapsTo_image π (domain ∩ good)) (finsetInjOn_inter good hπ)
    (finsetSurjOn_image π (domain ∩ good))
    (fun i hi ↦ hbridge i (Finset.mem_inter.mp hi).2)
    (fun i hi ↦ herr i (Finset.mem_inter.mp hi).2)
    (fun i hi ↦ hscale i (Finset.mem_inter.mp hi).2) X Z

end RelativeFunctorImprove
end GroupApproximation
