import GroupApproximation.KunThom.CountingEndgamePropsScale

/-!
# The one-sided inequalities of the relative data

`CompressorRelativeData.oneSided` is the producer `honesided` of the per-compressor
assembly (`CompressorNormalizationAssembly.seqNormalizes_of_compressor_of_frameSteps`):
every relative data satisfies `OneSided`.  This is Kun and Thom's (2) and (3)
(arXiv:2608.06222v3, §4, tex lines 1140–1193) for the arrow count, off the
non-clean objects.

* `orbit_sdiff_image_subset`: the part of an orbit outside the image of the
  inclusion of a restriction consists of unretained objects.
* `RelativeClusterFunctor.arrowCount_le_of_clean`: at a matched object `i` whose match
  `π i` has a clean orbit at scale `ζ ≤ 1/2`, `arrowCount (π i) ≤ (1 + 2ζ) arrowCount i`.
* `CompressorRelativeData.unretainedDensity`, `dirtyObjects` and `badObjects`: the
  density of the unretained objects of a compressor, the objects whose orbit meets
  them in more than the cleanliness scale, and the matched objects whose match is
  dirty.
* `sum_badObjects_le` and `mul_sum_dirtyObjects_le`: the bad objects weigh at most
  twice the dirty ones, and `ζ / 2` times the dirty weight is at most the unretained
  weight.
* `CompressorRelativeData.oneSided`.
-/

namespace GroupApproximation
namespace CountingEndgame

open CategoryTheory GroupoidPresentation CompressorNormalizationAssembly

universe u v

/-- The part of an orbit outside the image of the inclusion of `P.restrict R` consists
of objects outside `R`. -/
theorem orbit_sdiff_image_subset {I : Type u} [Fintype I] [DecidableEq I]
    (P : GroupoidPresentation.{u, v} I) (R : Finset I) (X : (P.restrict (R : Set I)).Obj) :
    FiniteGroupoid.orbit ((P.restrictInclusionFunctor (R : Set I)).obj X) \
        Finset.univ.image (P.restrictInclusionFunctor (R : Set I)).obj ⊆
      FiniteGroupoid.orbit ((P.restrictInclusionFunctor (R : Set I)).obj X) ∩
        (Finset.univ \ R).image (Obj.mk (P := P)) := by
  intro Z hZ
  obtain ⟨hZo, hZim⟩ := Finset.mem_sdiff.mp hZ
  refine Finset.mem_inter.mpr ⟨hZo, Finset.mem_image.mpr ⟨Z.val, ?_, rfl⟩⟩
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hZR ↦ hZim ?_⟩
  exact Finset.mem_image.mpr ⟨⟨⟨Z.val, Finset.mem_coe.mpr hZR⟩⟩, Finset.mem_univ _, rfl⟩

/-- **One-sided arrow count at a clean match.** -/
theorem RelativeClusterFunctor.arrowCount_le_of_clean {I : Type u} [Fintype I]
    [DecidableEq I] {P : GroupoidPresentation.{u, v} I} [∀ i j, Finite (P.Rep i j)]
    {Rt Mt : Finset I} (𝓕 : P.RelativeClusterFunctor Rt Mt) {i : I} (hi : i ∈ Mt) {ζ : ℝ}
    (hζ : 0 ≤ ζ) (hζ₂ : ζ ≤ 1 / 2)
    (hclean : ((FiniteGroupoid.orbit (⟨𝓕.π i⟩ : P.Obj) ∩
        (Finset.univ \ Rt).image (Obj.mk (P := P))).card : ℝ) ≤
      ζ * (FiniteGroupoid.orbit (⟨𝓕.π i⟩ : P.Obj)).card) :
    (ArrowCountMedian.arrowCount (⟨𝓕.π i⟩ : P.Obj) : ℝ) ≤
      (1 + 2 * ζ) * ArrowCountMedian.arrowCount (⟨i⟩ : P.Obj) := by
  haveI := 𝓕.faithful
  have hmem : 𝓕.π i ∈ (Rt : Set I) := 𝓕.mapsTo (Finset.mem_coe.mpr hi)
  have hF : Function.Injective
      (𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)).obj :=
    (P.restrictInclusionFunctor_obj_injective _).comp 𝓕.toFunctor_obj_injective
  have hsub := orbit_sdiff_image_subset P Rt ⟨⟨𝓕.π i, hmem⟩⟩
  have hclean' : ((FiniteGroupoid.orbit ((P.restrictInclusionFunctor (Rt : Set I)).obj
        ⟨⟨𝓕.π i, hmem⟩⟩) \
      Finset.univ.image (P.restrictInclusionFunctor (Rt : Set I)).obj).card : ℝ) ≤
      ζ * (FiniteGroupoid.orbit ((P.restrictInclusionFunctor (Rt : Set I)).obj
        ⟨⟨𝓕.π i, hmem⟩⟩)).card := by
    refine le_trans ?_ hclean
    exact_mod_cast Finset.card_le_card hsub
  have horb := mul_card_orbit_le_card_orbit_map_of_clean (P.restrictInclusionFunctor (Rt : Set I))
    (𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)) hF ⟨⟨𝓕.π i, hmem⟩⟩ hclean'
  have hvert := card_vertexGroup_le_card_vertexGroup_map
    (P.restrictInclusionFunctor (Rt : Set I))
    (𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)) ⟨⟨𝓕.π i, hmem⟩⟩
  have hFX : (𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)).obj
      ⟨⟨𝓕.π i, hmem⟩⟩ = (⟨i⟩ : P.Obj) := by
    show (⟨(𝓕.F.obj ⟨𝓕.π i, hmem⟩).1⟩ : P.Obj) = ⟨i⟩
    rw [𝓕.obj_π i hi]
  rw [hFX] at horb hvert
  have hko : (Fintype.card ((⟨𝓕.π i⟩ : P.Obj) ⟶ ⟨𝓕.π i⟩) : ℝ) ≤
      Fintype.card ((⟨i⟩ : P.Obj) ⟶ ⟨i⟩) := by
    exact_mod_cast hvert
  have ho0 : (0 : ℝ) ≤ (FiniteGroupoid.orbit (⟨i⟩ : P.Obj)).card := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ Fintype.card ((⟨𝓕.π i⟩ : P.Obj) ⟶ ⟨𝓕.π i⟩) := Nat.cast_nonneg _
  have horb' : (1 - ζ) * ((FiniteGroupoid.orbit (⟨𝓕.π i⟩ : P.Obj)).card : ℝ) ≤
      (FiniteGroupoid.orbit (⟨i⟩ : P.Obj)).card := horb
  have hmul : (1 - ζ) * (ArrowCountMedian.arrowCount (⟨𝓕.π i⟩ : P.Obj) : ℝ) ≤
      ArrowCountMedian.arrowCount (⟨i⟩ : P.Obj) := by
    rw [ArrowCountMedian.arrowCount_cast, ArrowCountMedian.arrowCount_cast]
    calc (1 - ζ) * (((FiniteGroupoid.orbit (⟨𝓕.π i⟩ : P.Obj)).card : ℝ) *
          Fintype.card ((⟨𝓕.π i⟩ : P.Obj) ⟶ ⟨𝓕.π i⟩))
        = ((1 - ζ) * (FiniteGroupoid.orbit (⟨𝓕.π i⟩ : P.Obj)).card) *
            Fintype.card ((⟨𝓕.π i⟩ : P.Obj) ⟶ ⟨𝓕.π i⟩) := by ring
      _ ≤ (FiniteGroupoid.orbit (⟨i⟩ : P.Obj)).card *
            Fintype.card ((⟨𝓕.π i⟩ : P.Obj) ⟶ ⟨𝓕.π i⟩) :=
          mul_le_mul_of_nonneg_right horb' hk0
      _ ≤ (FiniteGroupoid.orbit (⟨i⟩ : P.Obj)).card *
            Fintype.card ((⟨i⟩ : P.Obj) ⟶ ⟨i⟩) :=
          mul_le_mul_of_nonneg_left hko ho0
  exact ArrowCountMedian.le_one_add_two_mul_of_one_sub_mul_le (Nat.cast_nonneg _) hζ hζ₂ hmul

namespace CompressorRelativeData

open Classical in
/-- The density of the objects outside the retained family of `q` at index `n`. -/
noncomputable def unretainedDensity {G : Type} [Group G] {A : SoficApproximation G}
    {K : Type} [Group K] {ι : K →* G} {R : RetainedComponents A K ι} {t : G}
    {F : ClusterFrame R} (M : CompressorRelativeData t F) (q : G) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.univ \ M.retained q n, (Fintype.card ((F.embedding n).model i) : ℝ)) /
    (Fintype.card (A.model n) : ℝ)

open Classical in
/-- The objects whose orbit meets the unretained objects of `q` in more than the
cleanliness scale. -/
noncomputable def dirtyObjects {G : Type} [Group G] {A : SoficApproximation G}
    {K : Type} [Group K] {ι : K →* G} {R : RetainedComponents A K ι} {t : G}
    {F : ClusterFrame R} (M : CompressorRelativeData t F) (q : G) (n : ℕ) :
    Finset (F.Obj n) :=
  Finset.univ.filter fun i ↦
    cleanScale (M.unretainedDensity q) n *
        ((FiniteGroupoid.orbit (⟨i⟩ : (F.system n).presentation.Obj)).card : ℝ) <
      ((FiniteGroupoid.orbit (⟨i⟩ : (F.system n).presentation.Obj) ∩
        (Finset.univ \ M.retained q n).image (Obj.mk (P := (F.system n).presentation))).card : ℝ)

open Classical in
/-- The matched objects of `q` whose match is dirty. -/
noncomputable def badObjects {G : Type} [Group G] {A : SoficApproximation G}
    {K : Type} [Group K] {ι : K →* G} {R : RetainedComponents A K ι} {t : G}
    {F : ClusterFrame R} (M : CompressorRelativeData t F) (q : G) (n : ℕ) :
    Finset (F.Obj n) :=
  (M.matched q n).filter fun i ↦ M.matching q n i ∈ M.dirtyObjects q n

theorem unretainedDensity_nonneg {G : Type} [Group G] {A : SoficApproximation G}
    {K : Type} [Group K] {ι : K →* G} {R : RetainedComponents A K ι} {t : G}
    {F : ClusterFrame R} (M : CompressorRelativeData t F) (q : G) (n : ℕ) :
    0 ≤ M.unretainedDensity q n := by
  unfold unretainedDensity
  exact div_nonneg (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (Nat.cast_nonneg _)

open Classical in
/-- The bad objects weigh at most twice the dirty objects. -/
theorem sum_badObjects_le {G : Type} [Group G] {A : SoficApproximation G}
    {K : Type} [Group K] {ι : K →* G} {R : RetainedComponents A K ι} {t : G}
    {F : ClusterFrame R} (M : CompressorRelativeData t F) {q : G}
    (hq : q ∈ M.setup.compressors) (n : ℕ) :
    ∑ i ∈ M.badObjects q n, (Fintype.card ((F.embedding n).model i) : ℝ) ≤
      2 * ∑ i ∈ M.dirtyObjects q n, (Fintype.card ((F.embedding n).model i) : ℝ) := by
  have hinj : Set.InjOn (M.matching q n) (M.matched q n : Set (F.Obj n)) := by
    rw [M.matching_of_mem hq n]
    exact (M.functor q hq n).injOn
  have hsize : ∀ i ∈ M.matched q n, (Fintype.card ((F.embedding n).model i) : ℝ) ≤
      2 * Fintype.card ((F.embedding n).model (M.matching q n i)) := by
    intro i hi
    rw [M.matching_of_mem hq n]
    exact_mod_cast M.size_le q hq n i hi
  exact sum_filter_image_le (fun i ↦ (Fintype.card ((F.embedding n).model i) : ℝ))
    (fun _ ↦ Nat.cast_nonneg _) (M.matched q n) (M.dirtyObjects q n) (M.matching q n) hinj
    (by norm_num) hsize

open Classical in
/-- `ζ / 2` times the dirty weight is at most the unretained weight. -/
theorem mul_sum_dirtyObjects_le {G : Type} [Group G] {A : SoficApproximation G}
    {K : Type} [Group K] {ι : K →* G} {R : RetainedComponents A K ι} {t : G}
    {F : ClusterFrame R} (M : CompressorRelativeData t F) (q : G) (n : ℕ) :
    cleanScale (M.unretainedDensity q) n * (1 - 1 / 2) *
        ∑ i ∈ M.dirtyObjects q n, (Fintype.card ((F.embedding n).model i) : ℝ) ≤
      ∑ i ∈ Finset.univ \ M.retained q n, (Fintype.card ((F.embedding n).model i) : ℝ) := by
  have hmk : Set.InjOn (Obj.mk (P := (F.system n).presentation)) (Set.univ : Set (F.Obj n)) :=
    fun _ _ _ _ h ↦ congrArg Obj.val h
  have himage : ∀ s : Finset (F.Obj n),
      ∑ Z ∈ s.image (Obj.mk (P := (F.system n).presentation)),
          (Fintype.card ((F.system n).model Z.val) : ℝ) =
        ∑ i ∈ s, (Fintype.card ((F.embedding n).model i) : ℝ) := by
    intro s
    exact Finset.sum_image fun x _ y _ h ↦ hmk (Set.mem_univ x) (Set.mem_univ y) h
  have hdirty := mul_sum_le_of_dirty
    (fun Z : (F.system n).presentation.Obj ↦ (Fintype.card ((F.system n).model Z.val) : ℝ))
    (fun _ ↦ Nat.cast_nonneg _)
    ((Finset.univ \ M.retained q n).image (Obj.mk (P := (F.system n).presentation)))
    ((M.dirtyObjects q n).image (Obj.mk (P := (F.system n).presentation)))
    (by norm_num) (half_card_model_le_of_mem_orbit (F.system n))
    (fun Z hZ ↦ by
      obtain ⟨i, hi, hiZ⟩ := Finset.mem_image.mp hZ
      rw [← hiZ]
      exact (Finset.mem_filter.mp hi).2)
  rw [himage, himage] at hdirty
  exact hdirty

open Classical in
/-- **`honesided`.**  Every relative data satisfies the one-sided inequalities. -/
theorem oneSided {G : Type} [Group G] {A : SoficApproximation G}
    {K : Type} [Group K] {ι : K →* G} {R : RetainedComponents A K ι} {t : G}
    {F : ClusterFrame R} (M : CompressorRelativeData t F) : M.OneSided := by
  refine ⟨fun q n ↦ 2 * cleanScale (M.unretainedDensity q) n, M.badObjects,
    fun q _ n ↦ by have := cleanScale_pos (M.unretainedDensity q) n; linarith,
    fun q hq ↦ (vanishing_cleanScale (M.unretainedDensity_nonneg q)
      (M.unretained_negligible q hq)).const_mul 2, ?_, ?_⟩
  · intro q hq n i hi hbad
    have hnd : M.matching q n i ∉ M.dirtyObjects q n :=
      fun h ↦ hbad (Finset.mem_filter.mpr ⟨hi, h⟩)
    have hclean : ((FiniteGroupoid.orbit (⟨M.matching q n i⟩ : (F.system n).presentation.Obj) ∩
        (Finset.univ \ M.retained q n).image (Obj.mk (P := (F.system n).presentation))).card : ℝ) ≤
        cleanScale (M.unretainedDensity q) n *
          (FiniteGroupoid.orbit (⟨M.matching q n i⟩ : (F.system n).presentation.Obj)).card := by
      by_contra hcon
      exact hnd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_le.mp hcon⟩)
    rw [M.matching_of_mem hq n] at hclean ⊢
    exact RelativeClusterFunctor.arrowCount_le_of_clean (M.functor q hq n) hi
      (cleanScale_pos _ _).le (cleanScale_le_half _ _) hclean
  · intro q hq
    have hN : ∀ n, (0 : ℝ) ≤ Fintype.card (A.model n) := fun n ↦ Nat.cast_nonneg _
    refine Vanishing.squeeze (fun n ↦ div_nonneg (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
      (hN n)) (fun n ↦ ?_)
      ((vanishing_div_cleanScale (M.unretainedDensity_nonneg q)
        (M.unretained_negligible q hq)).const_mul 4)
    have hζ := cleanScale_pos (M.unretainedDensity q) n
    have hbad := M.sum_badObjects_le hq n
    have hdirty := M.mul_sum_dirtyObjects_le q n
    have hdirty' : ∑ i ∈ M.dirtyObjects q n, (Fintype.card ((F.embedding n).model i) : ℝ) ≤
        2 * (∑ i ∈ Finset.univ \ M.retained q n, (Fintype.card ((F.embedding n).model i) : ℝ)) /
          cleanScale (M.unretainedDensity q) n := by
      rw [le_div_iff₀ hζ]
      linarith
    show (∑ i ∈ M.badObjects q n, (Fintype.card ((F.embedding n).model i) : ℝ)) /
        (Fintype.card (A.model n) : ℝ) ≤
      4 * (M.unretainedDensity q n / cleanScale (M.unretainedDensity q) n)
    have hle : ∑ i ∈ M.badObjects q n, (Fintype.card ((F.embedding n).model i) : ℝ) ≤
        4 * (∑ i ∈ Finset.univ \ M.retained q n, (Fintype.card ((F.embedding n).model i) : ℝ)) /
          cleanScale (M.unretainedDensity q) n := by
      have h4 : 2 * (2 * (∑ i ∈ Finset.univ \ M.retained q n,
          (Fintype.card ((F.embedding n).model i) : ℝ)) / cleanScale (M.unretainedDensity q) n) =
          4 * (∑ i ∈ Finset.univ \ M.retained q n, (Fintype.card ((F.embedding n).model i) : ℝ)) /
            cleanScale (M.unretainedDensity q) n := by ring
      linarith
    calc (∑ i ∈ M.badObjects q n, (Fintype.card ((F.embedding n).model i) : ℝ)) /
          (Fintype.card (A.model n) : ℝ)
        ≤ (4 * (∑ i ∈ Finset.univ \ M.retained q n, (Fintype.card ((F.embedding n).model i) : ℝ)) /
            cleanScale (M.unretainedDensity q) n) / (Fintype.card (A.model n) : ℝ) :=
          div_le_div_of_nonneg_right hle (hN n)
      _ = 4 * (M.unretainedDensity q n / cleanScale (M.unretainedDensity q) n) := by
          unfold unretainedDensity
          ring

end CompressorRelativeData

end CountingEndgame
end GroupApproximation
