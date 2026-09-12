import GroupApproximation.KunThom.RelativeFunctorImproveWords
import GroupApproximation.KunThom.CompressorNormalizationAssemblyFrame

/-!
# The relative cluster functor of a compressor over a cluster frame

`CountingEndgame.CompressorRelativeData` asks, for every compressor `q` and index `n`,
for the bundled relative cluster functor of Kun--Thom, arXiv:2608.06222v3, Lemma 4.3,
between retained and matched objects of the cluster system `F.system n` of a
`ClusterFrame F`, and for matched objects at most twice the size of their matches.
This file produces both at one index and one compressor.

The frame's embedding `F.embedding n` and labels `F.action n` are definitionally the
ones of `RelativeFunctorImprove.relativeClusterFunctorOfWords` with the placement
`F.embedAt n`, and the distance bounds come from the frame.  Every remaining hypothesis
is pointwise at a matched object `i`, evaluated at the pair `(i, π i)` with
`u = A.map n q`:
- `hbridge`: `100 (sourceDefect + targetDefect)` of the bridge realized by `u` from `i` to
  `π i` is at most `scale (π i)`;
- `herr`: `40 (inError + outError)` of the bridge realized by `u⁻¹` from `π i` to `i` is
  at most `threshold n · scale (π i)`;
- `hscale`: `400 ≤ scale (π i)`.
The repair factor must satisfy `2 (1 + |T| k) ≤ K₀` for words of length at most `k`.

* `frameRelativeFunctor`: the functor between arbitrary `retained` and `matched`, for a
  matching `π` from `matched` onto `retained`; its matching is `π`
  (`frameRelativeFunctor_π`).
* `frame_size_le`: matched objects are at most twice the size of their matches.
* `frameRelativeFunctorOfGood` and `frame_size_le_of_good`: the same with
  `matched := domain ∩ good` and `retained := (domain ∩ good).image π`, for a matching
  injective on `domain` and hypotheses on `good`.
-/

namespace GroupApproximation
namespace RelativeFunctorImprove

open GroupoidPresentation CompressorNormalizationAssembly BlockPatching RelativeFunctorEstimate
open Classical

/-! ### Finite matchings -/

theorem finsetMapsTo_image {α : Type*} [DecidableEq α] (π : α → α) (s : Finset α) :
    Set.MapsTo π (s : Set α) ((s.image π : Finset α) : Set α) :=
  fun _ hx ↦ Finset.mem_coe.mpr (Finset.mem_image_of_mem π (Finset.mem_coe.mp hx))

theorem finsetSurjOn_image {α : Type*} [DecidableEq α] (π : α → α) (s : Finset α) :
    Set.SurjOn π (s : Set α) ((s.image π : Finset α) : Set α) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
  exact ⟨x, Finset.mem_coe.mpr hx, rfl⟩

theorem finsetInjOn_inter {α : Type*} [DecidableEq α] {domain : Finset α} (good : Finset α)
    {π : α → α} (hπ : Set.InjOn π (domain : Set α)) :
    Set.InjOn π ((domain ∩ good : Finset α) : Set α) :=
  fun _ hx _ hy h ↦ hπ (Finset.mem_coe.mpr (Finset.mem_inter.mp (Finset.mem_coe.mp hx)).1)
    (Finset.mem_coe.mpr (Finset.mem_inter.mp (Finset.mem_coe.mp hy)).1) h

/-! ### Pointwise hypotheses at the retained objects -/

/-- The bridge masses at a retained object, from the matched-object hypothesis. -/
theorem bridgeMass_le_of_matched {G : Type} [Group G] {A : SoficApproximation G} {K : Type}
    [Group K] {ι : K →* G} {R : RetainedComponents A K ι} (F : ClusterFrame R) (n : ℕ)
    (q : G) {matched retained : Finset (F.Obj n)} {π : F.Obj n → F.Obj n}
    (hsurj : Set.SurjOn π (matched : Set (F.Obj n)) (retained : Set (F.Obj n)))
    (hbridge : ∀ i ∈ matched,
      100 * (((F.embedding n).bridge (A.map n q) i (π i)).sourceDefect +
        ((F.embedding n).bridge (A.map n q) i (π i)).targetDefect) ≤ (F.system n).scale (π i))
    (X : ↥(retained : Set (F.Obj n))) :
    100 * (((F.embedding n).bridge (A.map n q)⁻¹ X.1
          (ClusterMetric.matchingInverse π hsurj X).1).sourceDefect +
        ((F.embedding n).bridge (A.map n q)⁻¹ X.1
          (ClusterMetric.matchingInverse π hsurj X).1).targetDefect) ≤
      (F.system n).scale X.1 := by
  have hm : (ClusterMetric.matchingInverse π hsurj X).1 ∈ matched :=
    Finset.mem_coe.mp (ClusterMetric.matchingInverse π hsurj X).2
  have h := hbridge _ hm
  rw [← targetDefect_bridge_inv (F.embedding n) (A.map n q)
      (ClusterMetric.matchingInverse π hsurj X).1 (π (ClusterMetric.matchingInverse π hsurj X).1),
    ← sourceDefect_bridge_inv (F.embedding n) (A.map n q)
      (ClusterMetric.matchingInverse π hsurj X).1 (π (ClusterMetric.matchingInverse π hsurj X).1),
    ClusterMetric.apply_matchingInverse π hsurj X] at h
  omega

/-- The localized errors at a retained object, from the matched-object hypothesis. -/
theorem errorMass_le_of_matched {G : Type} [Group G] {A : SoficApproximation G} {K : Type}
    [Group K] {ι : K →* G} {R : RetainedComponents A K ι} (F : ClusterFrame R) (n : ℕ)
    (q : G) (ws : ↥R.data.generators → List ↥R.data.generators)
    {matched retained : Finset (F.Obj n)} {π : F.Obj n → F.Obj n}
    (hsurj : Set.SurjOn π (matched : Set (F.Obj n)) (retained : Set (F.Obj n)))
    (herr : ∀ i ∈ matched,
      40 * ((inError (F.embedding n) (F.action n) (A.map n q)⁻¹ ws (π i) i +
        outError (F.embedding n) (F.action n) (A.map n q)⁻¹ ws (π i) i : ℕ) : ℝ) ≤
        F.threshold n * (F.system n).scale (π i))
    (X : ↥(retained : Set (F.Obj n))) :
    40 * ((inError (F.embedding n) (F.action n) (A.map n q)⁻¹ ws X.1
          (ClusterMetric.matchingInverse π hsurj X).1 +
        outError (F.embedding n) (F.action n) (A.map n q)⁻¹ ws X.1
          (ClusterMetric.matchingInverse π hsurj X).1 : ℕ) : ℝ) ≤
      F.threshold n * (F.system n).scale X.1 := by
  have hm : (ClusterMetric.matchingInverse π hsurj X).1 ∈ matched :=
    Finset.mem_coe.mp (ClusterMetric.matchingInverse π hsurj X).2
  have h := herr _ hm
  rw [ClusterMetric.apply_matchingInverse π hsurj X] at h
  exact h

/-- The scale bound at a retained object, from the matched-object hypothesis. -/
theorem scale_le_of_matched {G : Type} [Group G] {A : SoficApproximation G} {K : Type}
    [Group K] {ι : K →* G} {R : RetainedComponents A K ι} (F : ClusterFrame R) (n : ℕ)
    {matched retained : Finset (F.Obj n)} {π : F.Obj n → F.Obj n}
    (hsurj : Set.SurjOn π (matched : Set (F.Obj n)) (retained : Set (F.Obj n)))
    (hscale : ∀ i ∈ matched, 400 ≤ (F.system n).scale (π i))
    (X : ↥(retained : Set (F.Obj n))) : 400 ≤ (F.system n).scale X.1 := by
  have hm : (ClusterMetric.matchingInverse π hsurj X).1 ∈ matched :=
    Finset.mem_coe.mp (ClusterMetric.matchingInverse π hsurj X).2
  have h := hscale _ hm
  rw [ClusterMetric.apply_matchingInverse π hsurj X] at h
  exact h

/-! ### The functor and the size bound -/

/-- **The relative cluster functor of a compressor at one index of a cluster frame**
(Kun--Thom, Lemma 4.3), between `retained` and `matched`, for a matching `π` from
`matched` onto `retained` and the pointwise hypotheses at matched objects. -/
noncomputable def frameRelativeFunctor {G : Type} [Group G] {A : SoficApproximation G}
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
    (hscale : ∀ i ∈ matched, 400 ≤ (F.system n).scale (π i)) :
    (F.system n).presentation.RelativeClusterFunctor retained matched :=
  relativeClusterFunctorOfWords (F.system n) (F.embedAt n) (F.embedAt_injective n)
    (F.embedAt_disjoint n) (fun s ↦ A.map n (ι (s : K))) (A.map n q) ws hk hK₀ π hmaps hinj
    hsurj
    (fun X ↦ ((F.embedding n).bridge (A.map n q)⁻¹ X.1
        (ClusterMetric.matchingInverse π hsurj X).1).sourceDefect +
      ((F.embedding n).bridge (A.map n q)⁻¹ X.1
        (ClusterMetric.matchingInverse π hsurj X).1).targetDefect)
    (fun _ ↦ le_refl _)
    (bridgeMass_le_of_matched F n q hsurj hbridge)
    (errorMass_le_of_matched F n q ws hsurj herr)
    (F.distance_nonneg n) (F.distance_small n)
    (scale_le_of_matched F n hsurj hscale)

/-- The matching of `frameRelativeFunctor` is `π`. -/
theorem frameRelativeFunctor_π {G : Type} [Group G] {A : SoficApproximation G}
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
    (hscale : ∀ i ∈ matched, 400 ≤ (F.system n).scale (π i)) :
    (frameRelativeFunctor F n q ws hk hK₀ matched retained π hmaps hinj hsurj hbridge herr
      hscale).π = π :=
  rfl

/-- **Matched objects are at most twice the size of their matches**, from the bridge
masses. -/
theorem frame_size_le {G : Type} [Group G] {A : SoficApproximation G} {K : Type}
    [Group K] {ι : K →* G} {R : RetainedComponents A K ι} (F : ClusterFrame R) (n : ℕ)
    (q : G) (matched : Finset (F.Obj n)) (π : F.Obj n → F.Obj n)
    (hbridge : ∀ i ∈ matched,
      100 * (((F.embedding n).bridge (A.map n q) i (π i)).sourceDefect +
        ((F.embedding n).bridge (A.map n q) i (π i)).targetDefect) ≤ (F.system n).scale (π i)) :
    ∀ i ∈ matched, Fintype.card ((F.embedding n).model i) ≤
      2 * Fintype.card ((F.embedding n).model (π i)) := by
  intro i hi
  have hb := hbridge i hi
  have h1 := CentralizerNormalizationImprove.card_source_le_card_target_add
    ((F.embedding n).bridge (A.map n q) i (π i))
  have heq : (F.system n).scale (π i) = Fintype.card ((F.embedding n).model (π i)) / 18 :=
    (F.system n).scale_eq (π i)
  omega

/-! ### Matched objects from a domain and a set of good objects -/

/-- **The relative cluster functor with `matched := domain ∩ good`** and
`retained := (domain ∩ good).image π`, for a matching `π` injective on `domain` and the
pointwise hypotheses on `good`. -/
noncomputable def frameRelativeFunctorOfGood {G : Type} [Group G] {A : SoficApproximation G}
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
    (hscale : ∀ i ∈ good, 400 ≤ (F.system n).scale (π i)) :
    (F.system n).presentation.RelativeClusterFunctor ((domain ∩ good).image π)
      (domain ∩ good) :=
  frameRelativeFunctor F n q ws hk hK₀ (domain ∩ good) ((domain ∩ good).image π) π
    (finsetMapsTo_image π (domain ∩ good)) (finsetInjOn_inter good hπ)
    (finsetSurjOn_image π (domain ∩ good))
    (fun i hi ↦ hbridge i (Finset.mem_inter.mp hi).2)
    (fun i hi ↦ herr i (Finset.mem_inter.mp hi).2)
    (fun i hi ↦ hscale i (Finset.mem_inter.mp hi).2)

/-- The matching of `frameRelativeFunctorOfGood` is `π`. -/
theorem frameRelativeFunctorOfGood_π {G : Type} [Group G] {A : SoficApproximation G}
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
    (hscale : ∀ i ∈ good, 400 ≤ (F.system n).scale (π i)) :
    (frameRelativeFunctorOfGood F n q ws hk hK₀ domain good π hπ hbridge herr hscale).π = π :=
  rfl

/-- Matched objects of `frameRelativeFunctorOfGood` are at most twice the size of their
matches. -/
theorem frame_size_le_of_good {G : Type} [Group G] {A : SoficApproximation G} {K : Type}
    [Group K] {ι : K →* G} {R : RetainedComponents A K ι} (F : ClusterFrame R) (n : ℕ)
    (q : G) (domain good : Finset (F.Obj n)) (π : F.Obj n → F.Obj n)
    (hbridge : ∀ i ∈ good,
      100 * (((F.embedding n).bridge (A.map n q) i (π i)).sourceDefect +
        ((F.embedding n).bridge (A.map n q) i (π i)).targetDefect) ≤ (F.system n).scale (π i)) :
    ∀ i ∈ domain ∩ good, Fintype.card ((F.embedding n).model i) ≤
      2 * Fintype.card ((F.embedding n).model (π i)) :=
  frame_size_le F n q (domain ∩ good) π fun i hi ↦ hbridge i (Finset.mem_inter.mp hi).2

end RelativeFunctorImprove
end GroupApproximation
