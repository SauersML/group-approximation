import GroupApproximation.KunThom.RelativeDataErrors
import GroupApproximation.KunThom.SequentialComponentFamilyCompanion

/-!
# Good objects of a compressor over a cluster frame

`RelativeFunctorImprove.frameRelativeFunctorOfGood` builds the relative cluster functor of
Kun and Thom's Lemma 4.3 between `(domain ∩ good).image π` and `domain ∩ good` from three
bounds at every good object `X` and its match `π X`, with `u = A.map n q`:
- `hbridge`: `100 (sourceDefect + targetDefect)` of the bridge realized by `u` from `X` to
  `π X` is at most `scale (π X)`;
- `herr`: `40 (inError + outError)` of the bridge realized by `u⁻¹` from `π X` to `X` is at
  most `threshold n · scale (π X)`;
- `hscale`: `400 ≤ scale (π X)`.
This file takes for `domain` and `π` the retained domain and matching of a compressor
(`KunThom/ComponentCountingFrameObjects`), for the words `compressorWords C q`, and for
`good` the objects satisfying the three bounds.  Deleting the other objects costs negligible
weight when the matching error is `o(threshold)`: the scales eventually exceed `400`, the
bridge defects have negligible total, and the localized errors are charged to the matching
error at the threshold (Markov's inequality).

*Finite bounds.*

* `sum_compl_inter_le` and `sum_compl_image_inter_le`: the weight outside `domain ∩ good`,
  and outside its image, from the weight outside `domain` and its image, the bad weight of
  the domain, and the growth of the weight along the matching.
* `weight_le_of_not_good`: once the scale of the match is at least `400`, a bad object weighs
  at most `1901` times its bridge defects plus `800 / threshold` times its localized errors.
* `markov_div_le`: the normalized form of that bound.

*Good objects of a frame.*

* `IsGoodObject`, `goodObjects`, `badObjects` (the complement of `goodObjects`) and
  `matchedObjects = domain ∩ goodObjects`.
* `goodObjects_hbridge`, `goodObjects_herr`, `goodObjects_hscale` and `matchInjOn`: the
  hypotheses of `frameRelativeFunctorOfGood`.
* `frame_scale_eventually`, `frameBridgeError_sum_negligible` and `badWeight_negligible`:
  the bad objects of the domain have negligible weight; `badObjects_weight_negligible` states
  this for `domain ∩ badObjects`.
* `matchedObjects_unmatched_negligible`, `matchedObjects_unretained_negligible` and
  `matchedObjects_bridge_negligible`: `unmatched_negligible`, `unretained_negligible` for the
  image of the matched objects, and `bridge_negligible` of
  `CountingEndgame.CompressorRelativeData`.
-/

namespace GroupApproximation
namespace RelativeDataMarkov

open scoped BigOperators symmDiff

/-! ### Finite bounds -/

/-- The weight outside `domain ∩ good`. -/
theorem sum_compl_inter_le {ι : Type*} [Fintype ι] [DecidableEq ι] (dom : Finset ι)
    (P : ι → Prop) [DecidablePred P] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∑ i ∈ Finset.univ \ (dom ∩ Finset.univ.filter P), w i ≤
      ∑ i ∈ Finset.univ \ dom, w i + ∑ i ∈ dom, if P i then 0 else w i := by
  have hsub : Finset.univ \ (dom ∩ Finset.univ.filter P) ⊆
      (Finset.univ \ dom) ∪ dom.filter fun i ↦ ¬ P i := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_filter] at hi
    rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter]
    by_cases hD : i ∈ dom
    · exact Or.inr ⟨hD, fun hP ↦ hi.2 ⟨hD, Finset.mem_univ i, hP⟩⟩
    · exact Or.inl ⟨Finset.mem_univ i, hD⟩
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ ↦ hw i
  have hunion := Finset.sum_union_inter (s₁ := Finset.univ \ dom)
    (s₂ := dom.filter fun i ↦ ¬ P i) (f := w)
  have hinter : 0 ≤ ∑ i ∈ (Finset.univ \ dom) ∩ dom.filter (fun i ↦ ¬ P i), w i :=
    Finset.sum_nonneg fun i _ ↦ hw i
  have hfilter : ∑ i ∈ dom.filter (fun i ↦ ¬ P i), w i =
      ∑ i ∈ dom, if P i then 0 else w i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hp : P i
    · rw [if_pos hp, if_neg (not_not.mpr hp)]
    · rw [if_neg hp, if_pos hp]
  linarith

/-- The weight outside the image of `domain ∩ good`. -/
theorem sum_compl_image_inter_le {ι : Type*} [Fintype ι] [DecidableEq ι] (dom : Finset ι)
    (P : ι → Prop) [DecidablePred P] (π : ι → ι) (hinj : Set.InjOn π (dom : Set ι))
    (w β : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hβ : ∀ i, 0 ≤ β i)
    (hπ : ∀ i ∈ dom, w (π i) ≤ w i + β i) :
    ∑ j ∈ Finset.univ \ (dom ∩ Finset.univ.filter P).image π, w j ≤
      ∑ j ∈ Finset.univ \ dom.image π, w j + (∑ i ∈ dom, if P i then 0 else w i) +
        ∑ i ∈ dom, β i := by
  have hsub : Finset.univ \ (dom ∩ Finset.univ.filter P).image π ⊆
      (Finset.univ \ dom.image π) ∪ (dom.filter fun i ↦ ¬ P i).image π := by
    intro j hj
    by_cases hjD : j ∈ dom.image π
    · obtain ⟨i, hiD, rfl⟩ := Finset.mem_image.mp hjD
      refine Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiD, fun hP ↦ ?_⟩, rfl⟩)
      exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_image.mpr
        ⟨i, Finset.mem_inter.mpr ⟨hiD, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hP⟩⟩, rfl⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hjD⟩)
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ ↦ hw j
  have hunion := Finset.sum_union_inter (s₁ := Finset.univ \ dom.image π)
    (s₂ := (dom.filter fun i ↦ ¬ P i).image π) (f := w)
  have hinter : 0 ≤ ∑ j ∈ (Finset.univ \ dom.image π) ∩ (dom.filter fun i ↦ ¬ P i).image π,
      w j :=
    Finset.sum_nonneg fun j _ ↦ hw j
  have himage : ∑ j ∈ (dom.filter fun i ↦ ¬ P i).image π, w j =
      ∑ i ∈ dom.filter (fun i ↦ ¬ P i), w (π i) :=
    Finset.sum_image (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ dom)))
  have hfilt : ∑ i ∈ dom.filter (fun i ↦ ¬ P i), w (π i) ≤
      ∑ i ∈ dom, ((if P i then 0 else w i) + β i) := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    by_cases hp : P i
    · rw [if_pos hp, if_neg (not_not.mpr hp)]
      linarith [hβ i]
    · rw [if_neg hp, if_pos hp]
      exact hπ i hi
  rw [Finset.sum_add_distrib] at hfilt
  linarith

/-- **A bad object is small or costly.**  If the scale `s = |Z| / 18` of the match is at least
`400` and one of the three bounds fails, the object weighs at most `1901` times the bridge
defects plus `800 / τ` times the localized errors. -/
theorem weight_le_of_not_good {Y Z : FiniteModel} (b : FinitePartialBijection Y Z) {s : ℕ}
    (hs : s = Fintype.card Z / 18) {err τ : ℝ} (herr : 0 ≤ err) (hτ : 0 < τ)
    (hs400 : 400 ≤ s)
    (hnot : ¬ (100 * (b.sourceDefect + b.targetDefect) ≤ s ∧ 40 * err ≤ τ * s ∧ 400 ≤ s)) :
    (Fintype.card Y : ℝ) ≤
      1901 * ((b.sourceDefect + b.targetDefect : ℕ) : ℝ) + 800 / τ * err := by
  have hsrc := CentralizerNormalizationImprove.card_source_le_card_target_add b
  have hZ : 18 * s ≤ Fintype.card Z ∧ Fintype.card Z < 18 * s + 18 := by omega
  have hterm : 0 ≤ 800 / τ * err := mul_nonneg (div_nonneg (by norm_num) hτ.le) herr
  by_cases h1 : 100 * (b.sourceDefect + b.targetDefect) ≤ s
  · have h2 : ¬ 40 * err ≤ τ * s := fun h2 ↦ hnot ⟨h1, h2, hs400⟩
    have hY : Fintype.card Y ≤ 20 * s := by omega
    have hYr : (Fintype.card Y : ℝ) ≤ 20 * (s : ℝ) := by exact_mod_cast hY
    have hlt : τ * (s : ℝ) < 40 * err := not_le.mp h2
    have h800 : 20 * (s : ℝ) ≤ 800 / τ * err := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hτ]
      linarith
    have hβ : (0 : ℝ) ≤ ((b.sourceDefect + b.targetDefect : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  · have hY : Fintype.card Y ≤ 1901 * (b.sourceDefect + b.targetDefect) := by omega
    have hYr : (Fintype.card Y : ℝ) ≤ 1901 * ((b.sourceDefect + b.targetDefect : ℕ) : ℝ) := by
      exact_mod_cast hY
    linarith

/-- The normalized form of the deletion bound. -/
theorem markov_div_le {S B W N τ m : ℝ} (hN : 0 ≤ N) (hτ : 0 < τ)
    (hS : S ≤ 1901 * B + 800 / τ * W) (hW : W / N ≤ m) :
    S / N ≤ 1901 * (B / N) + 800 * (m / τ) := by
  have h1 : S / N ≤ (1901 * B + 800 / τ * W) / N := div_le_div_of_nonneg_right hS hN
  have h2 : (1901 * B + 800 / τ * W) / N = 1901 * (B / N) + 800 * (W / N / τ) := by ring
  have h3 : W / N / τ ≤ m / τ := div_le_div_of_nonneg_right hW hτ.le
  linarith

/-! ### Good objects of a frame -/

open Classical
open CompressorNormalizationAssembly CompressorNormalizationAssembly.ClusterFrame

/-- The three bounds of `frameRelativeFunctorOfGood` at an object and its match. -/
def IsGoodObject {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) (q : G) (n : ℕ)
    (X : F.Obj n) : Prop :=
  100 * (((F.embedding n).bridge (A.map n q) X
      (D.toLocal.compressorMatch (matchingParent D F) q n X)).sourceDefect +
    ((F.embedding n).bridge (A.map n q) X
      (D.toLocal.compressorMatch (matchingParent D F) q n X)).targetDefect) ≤
      (F.system n).scale (D.toLocal.compressorMatch (matchingParent D F) q n X) ∧
    40 * ((RelativeFunctorImprove.inError (F.embedding n) (F.action n) (A.map n q)⁻¹
        (compressorWords C q) (D.toLocal.compressorMatch (matchingParent D F) q n X) X +
      RelativeFunctorImprove.outError (F.embedding n) (F.action n) (A.map n q)⁻¹
        (compressorWords C q) (D.toLocal.compressorMatch (matchingParent D F) q n X) X :
        ℕ) : ℝ) ≤
      F.threshold n * (F.system n).scale (D.toLocal.compressorMatch (matchingParent D F) q n X) ∧
    400 ≤ (F.system n).scale (D.toLocal.compressorMatch (matchingParent D F) q n X)

/-- The good objects of a compressor. -/
noncomputable def goodObjects {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) (q : G) (n : ℕ) :
    Finset (F.Obj n) :=
  Finset.univ.filter (IsGoodObject D F q n)

/-- The bad objects of a compressor: the complement of `goodObjects`. -/
noncomputable def badObjects {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) (q : G) (n : ℕ) :
    Finset (F.Obj n) :=
  Finset.univ.filter fun X ↦ ¬ IsGoodObject D F q n X

/-- The matched objects of a compressor: the retained domain restricted to good objects. -/
noncomputable def matchedObjects {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) (q : G) (n : ℕ) :
    Finset (F.Obj n) :=
  D.toLocal.compressorDomains (matchingParent D F) q n ∩ goodObjects D F q n

theorem goodObjects_hbridge {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) (q : G) (n : ℕ) :
    ∀ i ∈ goodObjects D F q n,
      100 * (((F.embedding n).bridge (A.map n q) i
          (D.toLocal.compressorMatch (matchingParent D F) q n i)).sourceDefect +
        ((F.embedding n).bridge (A.map n q) i
          (D.toLocal.compressorMatch (matchingParent D F) q n i)).targetDefect) ≤
        (F.system n).scale (D.toLocal.compressorMatch (matchingParent D F) q n i) :=
  fun _ hi ↦ And.left (Finset.mem_filter.mp hi).2

theorem goodObjects_herr {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) (q : G) (n : ℕ) :
    ∀ i ∈ goodObjects D F q n,
      40 * ((RelativeFunctorImprove.inError (F.embedding n) (F.action n) (A.map n q)⁻¹
          (compressorWords C q) (D.toLocal.compressorMatch (matchingParent D F) q n i) i +
        RelativeFunctorImprove.outError (F.embedding n) (F.action n) (A.map n q)⁻¹
          (compressorWords C q) (D.toLocal.compressorMatch (matchingParent D F) q n i) i :
          ℕ) : ℝ) ≤
        F.threshold n *
          (F.system n).scale (D.toLocal.compressorMatch (matchingParent D F) q n i) :=
  fun _ hi ↦ And.left (And.right (Finset.mem_filter.mp hi).2)

theorem goodObjects_hscale {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) (q : G) (n : ℕ) :
    ∀ i ∈ goodObjects D F q n,
      400 ≤ (F.system n).scale (D.toLocal.compressorMatch (matchingParent D F) q n i) :=
  fun _ hi ↦ And.right (And.right (Finset.mem_filter.mp hi).2)

/-- The matching of a compressor is injective on its retained domain. -/
theorem matchInjOn {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) {q : G}
    (hq : q ∈ C.compressors) (n : ℕ) :
    Set.InjOn (D.toLocal.compressorMatch (matchingParent D F) q n)
      (D.toLocal.compressorDomains (matchingParent D F) q n : Set (F.Obj n)) := by
  rw [D.toLocal.compressorDomains_of_mem (matchingParent D F) hq n]
  exact D.toLocal.injOn_compressorMatch (matchingParent_injective D F) hq n

/-! ### Negligible bad weight -/

/-- The scales of the objects of a frame eventually exceed any bound. -/
theorem frame_scale_eventually {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) (M : ℕ) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ X : F.Obj n, M ≤ (F.system n).scale X := by
  obtain ⟨N₀, hN₀⟩ := SequentialComponentFamily.componentFamily_scale_eventually D.gamma
    C.generatorsΓ_symmetric C.generatorsΓ_generate ⟨1, C.generatorsΓ_one⟩ D.enum
    D.enum_surjective M
  exact ⟨N₀, fun n hn X ↦ hN₀ n hn X.1⟩

/-- The bridge defects along the matching have negligible total over the domain. -/
theorem frameBridgeError_sum_negligible {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) {q : G}
    (hq : q ∈ C.compressors) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ X ∈ D.toLocal.compressorDomains (matchingParent D F) q n,
        ((((F.embedding n).bridge (A.map n q) X
            (D.toLocal.compressorMatch (matchingParent D F) q n X)).sourceDefect +
          ((F.embedding n).bridge (A.map n q) X
            (D.toLocal.compressorMatch (matchingParent D F) q n X)).targetDefect : ℕ) : ℝ) := by
  refine Negligible.mono_nonneg (fun _ ↦ Nat.cast_nonneg _)
    (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (fun n ↦ ?_)
    (D.toLocal.compressorDomain_symmDiff_negligible (fun n ↦ F.embedding n)
      (matchingParent_injective D F) (objectImage_subset_matchingParent D F)
      (matchingRemovedMass_negligible D F) hq)
  rw [D.toLocal.compressorDomains_of_mem (matchingParent D F) hq n]
  exact Finset.sum_le_sum fun X _ ↦ Nat.cast_le.mpr
    (RelativeFunctorEstimate.sourceDefect_add_targetDefect_bridge_le_objectImage
      (F.embedding n) (A.map n q) X (D.toLocal.compressorMatch (matchingParent D F) q n X))

/-- **Deleted weight.**  When the matching error is `o(threshold)`, the bad objects of the
retained domain carry negligible weight. -/
theorem badWeight_negligible {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) {q : G}
    (hq : q ∈ C.compressors) (hdens : Vanishing fun n ↦ matchingError D n / F.threshold n) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ X ∈ D.toLocal.compressorDomains (matchingParent D F) q n,
        if IsGoodObject D F q n X then 0 else (Fintype.card ((F.embedding n).model X) : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := frame_scale_eventually D F 400
  refine Vanishing.squeeze_eventually
    ((Vanishing.const_mul 1901 (frameBridgeError_sum_negligible D F hq)).add
      (Vanishing.const_mul 800 hdens)) N₀ fun n hn ↦ ⟨?_, ?_⟩
  · refine div_nonneg (Finset.sum_nonneg fun X _ ↦ ?_) (Nat.cast_nonneg _)
    split_ifs
    · exact le_rfl
    · exact Nat.cast_nonneg _
  · have hτ := F.threshold_pos n
    have hterm : ∀ X ∈ D.toLocal.compressorDomains (matchingParent D F) q n,
        (if IsGoodObject D F q n X then 0 else (Fintype.card ((F.embedding n).model X) : ℝ)) ≤
          1901 * ((((F.embedding n).bridge (A.map n q) X
              (D.toLocal.compressorMatch (matchingParent D F) q n X)).sourceDefect +
            ((F.embedding n).bridge (A.map n q) X
              (D.toLocal.compressorMatch (matchingParent D F) q n X)).targetDefect : ℕ) : ℝ) +
          800 / F.threshold n *
            ((RelativeFunctorImprove.inError (F.embedding n) (F.action n) (A.map n q)⁻¹
                (compressorWords C q) (D.toLocal.compressorMatch (matchingParent D F) q n X) X +
              RelativeFunctorImprove.outError (F.embedding n) (F.action n) (A.map n q)⁻¹
                (compressorWords C q) (D.toLocal.compressorMatch (matchingParent D F) q n X) X :
                ℕ) : ℝ) := by
      intro X _
      split_ifs with hgood
      · exact add_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
          (mul_nonneg (div_nonneg (by norm_num) hτ.le) (Nat.cast_nonneg _))
      · exact weight_le_of_not_good ((F.embedding n).bridge (A.map n q) X
          (D.toLocal.compressorMatch (matchingParent D F) q n X))
          ((F.system n).scale_eq (D.toLocal.compressorMatch (matchingParent D F) q n X))
          (Nat.cast_nonneg _) hτ
          (hN₀ n hn (D.toLocal.compressorMatch (matchingParent D F) q n X)) hgood
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    exact markov_div_le (Nat.cast_nonneg _) hτ hsum
      (frame_wordError_div_le_matchingError D F hq n)

/-- **The bad objects of the retained domain carry negligible weight.** -/
theorem badObjects_weight_negligible {G : Type} [Group G] {Γ : Subgroup G} [Infinite ↥Γ]
    {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) {q : G}
    (hq : q ∈ C.compressors) (hdens : Vanishing fun n ↦ matchingError D n / F.threshold n) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ X ∈ D.toLocal.compressorDomains (matchingParent D F) q n ∩ badObjects D F q n,
        (Fintype.card ((F.embedding n).model X) : ℝ) := by
  refine (badWeight_negligible D F hq hdens).congr fun n ↦ ?_
  have hset : D.toLocal.compressorDomains (matchingParent D F) q n ∩ badObjects D F q n =
      (D.toLocal.compressorDomains (matchingParent D F) q n).filter
        fun X ↦ ¬ IsGoodObject D F q n X := by
    ext X
    simp only [badObjects, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun X _ ↦ ?_
  by_cases hg : IsGoodObject D F q n X
  · rw [if_pos hg, if_neg (not_not.mpr hg)]
  · rw [if_neg hg, if_pos hg]

/-! ### Fields of the relative data -/

/-- **Unmatched weight** of the matched objects. -/
theorem matchedObjects_unmatched_negligible {G : Type} [Group G] {Γ : Subgroup G}
    [Infinite ↥Γ] {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) {q : G}
    (hq : q ∈ C.compressors) (hdens : Vanishing fun n ↦ matchingError D n / F.threshold n) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ X ∈ Finset.univ \ matchedObjects D F q n,
        (Fintype.card ((F.embedding n).model X) : ℝ) := by
  refine Negligible.mono_nonneg (fun _ ↦ Nat.cast_nonneg _)
    (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (fun n ↦ ?_)
    ((matchingUnmatched_negligible D F q hq).add (badWeight_negligible D F hq hdens))
  exact sum_compl_inter_le (D.toLocal.compressorDomains (matchingParent D F) q n)
    (IsGoodObject D F q n) (fun X ↦ (Fintype.card ((F.embedding n).model X) : ℝ))
    fun _ ↦ Nat.cast_nonneg _

/-- **Unretained weight** for the image of the matched objects. -/
theorem matchedObjects_unretained_negligible {G : Type} [Group G] {Γ : Subgroup G}
    [Infinite ↥Γ] {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) {q : G}
    (hq : q ∈ C.compressors) (hdens : Vanishing fun n ↦ matchingError D n / F.threshold n) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ X ∈ Finset.univ \ (matchedObjects D F q n).image
          (D.toLocal.compressorMatch (matchingParent D F) q n),
        (Fintype.card ((F.embedding n).model X) : ℝ) := by
  refine Negligible.mono_nonneg (fun _ ↦ Nat.cast_nonneg _)
    (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (fun n ↦ ?_)
    (((matchingUnimaged_negligible D F q hq).add (badWeight_negligible D F hq hdens)).add
      (frameBridgeError_sum_negligible D F hq))
  refine sum_compl_image_inter_le (D.toLocal.compressorDomains (matchingParent D F) q n)
    (IsGoodObject D F q n) (D.toLocal.compressorMatch (matchingParent D F) q n)
    (matchInjOn D F hq n) (fun X ↦ (Fintype.card ((F.embedding n).model X) : ℝ))
    (fun X ↦ ((((F.embedding n).bridge (A.map n q) X
        (D.toLocal.compressorMatch (matchingParent D F) q n X)).sourceDefect +
      ((F.embedding n).bridge (A.map n q) X
        (D.toLocal.compressorMatch (matchingParent D F) q n X)).targetDefect : ℕ) : ℝ))
    (fun _ ↦ Nat.cast_nonneg _) (fun _ ↦ Nat.cast_nonneg _) fun X _ ↦ ?_
  have h := CentralizerNormalizationImprove.card_target_le_card_source_add
    ((F.embedding n).bridge (A.map n q) X
      (D.toLocal.compressorMatch (matchingParent D F) q n X))
  have h' : Fintype.card ((F.embedding n).model
        (D.toLocal.compressorMatch (matchingParent D F) q n X)) ≤
      Fintype.card ((F.embedding n).model X) +
        (((F.embedding n).bridge (A.map n q) X
          (D.toLocal.compressorMatch (matchingParent D F) q n X)).sourceDefect +
        ((F.embedding n).bridge (A.map n q) X
          (D.toLocal.compressorMatch (matchingParent D F) q n X)).targetDefect) := by
    omega
  exact_mod_cast h'

/-- **Missing bridge mass** along the matched objects. -/
theorem matchedObjects_bridge_negligible {G : Type} [Group G] {Γ : Subgroup G}
    [Infinite ↥Γ] {C : CompressionSetup G ↥Γ PUnit.{1}} {A : SoficApproximation G}
    (D : CompressorDecomposition C A) (F : ClusterFrame D.retained) {q : G}
    (hq : q ∈ C.compressors) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ X ∈ matchedObjects D F q n,
        (((F.embedding n).bridge (A.map n q) X
          (D.toLocal.compressorMatch (matchingParent D F) q n X)).sourceDefect : ℝ) := by
  refine Negligible.mono_nonneg (fun _ ↦ Nat.cast_nonneg _)
    (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (fun n ↦ ?_)
    (matchingBridge_negligible D F q hq)
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun _ hX ↦ (Finset.mem_inter.mp hX).1)
    fun _ _ _ ↦ Nat.cast_nonneg _

end RelativeDataMarkov
end GroupApproximation
