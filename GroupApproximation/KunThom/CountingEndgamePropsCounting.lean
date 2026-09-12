import GroupApproximation.KunThom.CountingEndgamePropsSelect

/-!
# Transported bisections

`CompressorRelativeData.transported` is the producer `hcounting` of the per-compressor
assembly (`CompressorNormalizationAssembly.seqNormalizes_of_compressor_of_frameSteps`):
under concentration, every sequence of total bisections has a transported sequence.

This is the counting of Kun and Thom's proof of Theorem 4.1 (arXiv:2608.06222v3, §4,
tex lines 1218–1313).
* At every index the bisection `b n` is the lift
  `RelativeClusterFunctor.exists_bisection_lift` of `a n`, on the selected objects of
  `CountingEndgame.selected`.
* An object outside the image of the selected objects is unmatched, bad or violates
  the squared ratio bounds, or its image under the bisection is.
* Pulling a family back through the bisection at most doubles its weight, because
  sizes at most double along arrows.
* The weights of the unmatched objects, the bad objects and the objects violating the
  ratio bounds are negligible, the last one by concentration at `η = 1/64`.  Once the
  cleanliness scale is below `1/4`, the complement of the image of the selected
  objects weighs at most three times their sum.

* `sum_le_add_of_subset_union`, `sum_le_six_of_subset`: union bounds for nonnegative
  weights.
* `CompressorRelativeData.badObjects_negligible`.
* `CompressorRelativeData.sum_compl_selected_le`: the finite bound at one index.
* `CompressorRelativeData.transported`.
-/

namespace GroupApproximation
namespace CountingEndgame

open CategoryTheory GroupoidPresentation CompressorNormalizationAssembly

/-- Union bound for a nonnegative weight. -/
theorem sum_le_add_of_subset_union {ι : Type*} [DecidableEq ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) {s t r : Finset ι} (h : s ⊆ t ∪ r) :
    ∑ i ∈ s, w i ≤ ∑ i ∈ t, w i + ∑ i ∈ r, w i := by
  have h₁ : ∑ i ∈ s, w i ≤ ∑ i ∈ t ∪ r, w i :=
    Finset.sum_le_sum_of_subset_of_nonneg h fun i _ _ ↦ hw i
  have h₂ : (∑ i ∈ t ∪ r, w i) + ∑ i ∈ t ∩ r, w i = (∑ i ∈ t, w i) + ∑ i ∈ r, w i :=
    Finset.sum_union_inter
  have h₃ : 0 ≤ ∑ i ∈ t ∩ r, w i := Finset.sum_nonneg fun i _ ↦ hw i
  linarith

/-- Union bound over six families for a nonnegative weight. -/
theorem sum_le_six_of_subset {ι : Type*} [DecidableEq ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    {s t₁ t₂ t₃ t₄ t₅ t₆ : Finset ι} (h : s ⊆ t₁ ∪ (t₂ ∪ (t₃ ∪ (t₄ ∪ (t₅ ∪ t₆))))) :
    ∑ i ∈ s, w i ≤ ∑ i ∈ t₁, w i + ∑ i ∈ t₂, w i + ∑ i ∈ t₃, w i + ∑ i ∈ t₄, w i +
      ∑ i ∈ t₅, w i + ∑ i ∈ t₆, w i := by
  have h1 := sum_le_add_of_subset_union w hw h
  have h2 := sum_le_add_of_subset_union w hw (Finset.Subset.refl (t₂ ∪ (t₃ ∪ (t₄ ∪ (t₅ ∪ t₆)))))
  have h3 := sum_le_add_of_subset_union w hw (Finset.Subset.refl (t₃ ∪ (t₄ ∪ (t₅ ∪ t₆))))
  have h4 := sum_le_add_of_subset_union w hw (Finset.Subset.refl (t₄ ∪ (t₅ ∪ t₆)))
  have h5 := sum_le_add_of_subset_union w hw (Finset.Subset.refl (t₅ ∪ t₆))
  linarith

namespace CompressorRelativeData

open Classical in
/-- The bad objects of a compressor have negligible weight. -/
theorem badObjects_negligible {G : Type} [Group G] {A : SoficApproximation G}
    {K : Type} [Group K] {ι : K →* G} {R : RetainedComponents A K ι} {t : G}
    {F : ClusterFrame R} (M : CompressorRelativeData t F) {q : G}
    (hq : q ∈ M.setup.compressors) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ i ∈ M.badObjects q n, (Fintype.card ((F.embedding n).model i) : ℝ) := by
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

open Classical in
/-- **The finite counting bound at one index.**  If `1 + 16η < 2 (1 - ζ)` for the
cleanliness scale `ζ`, the objects outside the image of the selected objects weigh at
most three times the unmatched, bad and ratio-violating objects together. -/
theorem sum_compl_selected_le {G : Type} [Group G] {A : SoficApproximation G}
    {K : Type} [Group K] {ι : K →* G} {R : RetainedComponents A K ι} {t : G}
    {F : ClusterFrame R} (M : CompressorRelativeData t F) (a : ∀ n, F.Bis n) (n : ℕ)
    {η : ℝ} (hη : 0 ≤ η) (hη₁ : η ≤ 1 / 16)
    (hηζ : 1 + 16 * η < 2 * (1 - cleanScale (M.unretainedDensity t) n)) :
    ∑ i ∈ Finset.univ \ (selected (M.liftFunctor n) (a n)
        (targetChoice (M.liftFunctor n) (a n))).image (fun X ↦ ((M.liftFunctor n).obj X).val),
        (Fintype.card ((F.embedding n).model i) : ℝ) ≤
      3 * (∑ i ∈ Finset.univ \ M.matched t n, (Fintype.card ((F.embedding n).model i) : ℝ) +
        ∑ i ∈ M.badObjects t n, (Fintype.card ((F.embedding n).model i) : ℝ) +
        ∑ i ∈ (M.matched t n).filter (fun i ↦
            ¬ ((1 - 2 * η) ^ 2 * (observable F n (M.matching t n i) : ℝ) ≤
                (1 + 2 * η) ^ 2 * observable F n i ∧
              (1 - 2 * η) ^ 2 * (observable F n i : ℝ) ≤
                (1 + 2 * η) ^ 2 * observable F n (M.matching t n i))),
          (Fintype.card ((F.embedding n).model i) : ℝ)) := by
  have hw : ∀ i : F.Obj n, (0 : ℝ) ≤ Fintype.card ((F.embedding n).model i) :=
    fun _ ↦ Nat.cast_nonneg _
  have hπ := M.matching_of_mem M.mem_compressors n
  -- pulling a family back through the bisection at most doubles its weight
  have hpull : ∀ T : Finset (F.Obj n),
      ∑ i ∈ Finset.univ.filter (fun i ↦ ((a n).objEquiv ⟨i⟩).val ∈ T),
          (Fintype.card ((F.embedding n).model i) : ℝ) ≤
        2 * ∑ j ∈ T, (Fintype.card ((F.embedding n).model j) : ℝ) := by
    intro T
    have hinj : Set.InjOn (fun i : F.Obj n ↦ ((a n).objEquiv ⟨i⟩).val)
        ((Finset.univ : Finset (F.Obj n)) : Set (F.Obj n)) := by
      intro x _ y _ h
      have h' : (a n).objEquiv ⟨x⟩ = (a n).objEquiv ⟨y⟩ := congrArg Obj.mk h
      exact congrArg Obj.val ((a n).objEquiv.injective h')
    exact sum_filter_image_le (fun i ↦ (Fintype.card ((F.embedding n).model i) : ℝ)) hw
      Finset.univ T (fun i ↦ ((a n).objEquiv ⟨i⟩).val) hinj (by norm_num)
      fun i _ ↦ by exact_mod_cast card_model_le_two_mul_of_hom (F.system n) ((a n).hom ⟨i⟩)
  -- the complement of the image of the selected objects
  have hsub : Finset.univ \ (selected (M.liftFunctor n) (a n)
      (targetChoice (M.liftFunctor n) (a n))).image (fun X ↦ ((M.liftFunctor n).obj X).val) ⊆
      (Finset.univ \ M.matched t n) ∪
        ((Finset.univ.filter fun i ↦ ((a n).objEquiv ⟨i⟩).val ∈ Finset.univ \ M.matched t n) ∪
          (M.badObjects t n ∪
            ((Finset.univ.filter fun i ↦ ((a n).objEquiv ⟨i⟩).val ∈ M.badObjects t n) ∪
              ((M.matched t n).filter (fun i ↦
                  ¬ ((1 - 2 * η) ^ 2 * (observable F n (M.matching t n i) : ℝ) ≤
                      (1 + 2 * η) ^ 2 * observable F n i ∧
                    (1 - 2 * η) ^ 2 * (observable F n i : ℝ) ≤
                      (1 + 2 * η) ^ 2 * observable F n (M.matching t n i))) ∪
                Finset.univ.filter fun i ↦ ((a n).objEquiv ⟨i⟩).val ∈
                  (M.matched t n).filter (fun i ↦
                    ¬ ((1 - 2 * η) ^ 2 * (observable F n (M.matching t n i) : ℝ) ≤
                        (1 + 2 * η) ^ 2 * observable F n i ∧
                      (1 - 2 * η) ^ 2 * (observable F n i : ℝ) ≤
                        (1 + 2 * η) ^ 2 * observable F n (M.matching t n i))))))) := by
    intro i hi
    by_contra hcon
    apply (Finset.mem_sdiff.mp hi).2
    have hiM : i ∈ M.matched t n := by
      by_contra h
      exact hcon (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h⟩))
    have hjM : ((a n).objEquiv ⟨i⟩).val ∈ M.matched t n := by
      by_contra h
      exact hcon (Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩⟩)))
    have hibad : i ∉ M.badObjects t n := fun h ↦
      hcon (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _ h)))
    have hjbad : ((a n).objEquiv ⟨i⟩).val ∉ M.badObjects t n := fun h ↦
      hcon (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)))))
    have hisq := fun h ↦ hcon (Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hiM, h⟩))))))
    have hjsq := fun h ↦ hcon (Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i, Finset.mem_filter.mpr ⟨hjM, h⟩⟩))))))
    have hclean : ((FiniteGroupoid.orbit (⟨M.matching t n i⟩ : (F.system n).presentation.Obj) ∩
        (Finset.univ \ M.retained t n).image (Obj.mk (P := (F.system n).presentation))).card : ℝ) ≤
        cleanScale (M.unretainedDensity t) n *
          (FiniteGroupoid.orbit (⟨M.matching t n i⟩ : (F.system n).presentation.Obj)).card := by
      by_contra h
      exact hibad (Finset.mem_filter.mpr ⟨hiM, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        not_le.mp h⟩⟩)
    have hclean' : ((FiniteGroupoid.orbit
        (⟨M.matching t n ((a n).objEquiv ⟨i⟩).val⟩ : (F.system n).presentation.Obj) ∩
        (Finset.univ \ M.retained t n).image (Obj.mk (P := (F.system n).presentation))).card : ℝ) ≤
        cleanScale (M.unretainedDensity t) n *
          (FiniteGroupoid.orbit
            (⟨M.matching t n ((a n).objEquiv ⟨i⟩).val⟩ : (F.system n).presentation.Obj)).card := by
      by_contra h
      exact hjbad (Finset.mem_filter.mpr ⟨hjM, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        not_le.mp h⟩⟩)
    have hsq := (not_not.mp hisq).2
    have hsq' := (not_not.mp hjsq).2
    rw [hπ] at hclean hclean' hsq hsq'
    exact RelativeClusterFunctor.mem_image_selected (M.functor t M.mem_compressors n) (a n) hiM
      hjM hη hη₁ hηζ hclean hclean' hsq hsq'
  have hsix := sum_le_six_of_subset (fun i ↦ (Fintype.card ((F.embedding n).model i) : ℝ)) hw hsub
  have hp1 := hpull (Finset.univ \ M.matched t n)
  have hp3 := hpull (M.badObjects t n)
  have hp5 := hpull ((M.matched t n).filter (fun i ↦
    ¬ ((1 - 2 * η) ^ 2 * (observable F n (M.matching t n i) : ℝ) ≤
        (1 + 2 * η) ^ 2 * observable F n i ∧
      (1 - 2 * η) ^ 2 * (observable F n i : ℝ) ≤
        (1 + 2 * η) ^ 2 * observable F n (M.matching t n i))))
  linarith

open Classical in
/-- **`hcounting`.**  Under concentration every sequence of total bisections has a
transported sequence. -/
theorem transported {G : Type} [Group G] {A : SoficApproximation G}
    {K : Type} [Group K] {ι : K →* G} {R : RetainedComponents A K ι} {t : G}
    {F : ClusterFrame R} (M : CompressorRelativeData t F) (hM : M.Concentrated)
    (a : ∀ n, F.Bis n) : ∃ b : ∀ n, F.Bis n, M.Transported a b := by
  have hb : ∀ n, ∃ b : F.Bis n, ∀ X (hX : X ∈ selected (M.liftFunctor n) (a n)
      (targetChoice (M.liftFunctor n) (a n))),
      ∃ g : X ⟶ targetChoice (M.liftFunctor n) (a n) X,
        (M.liftFunctor n).map g = (a n).hom ((M.liftFunctor n).obj X) ≫
          eqToHom ((mem_selected _ (a n) _ X).mp hX).1.symm ∧
        ∃ e : b.objEquiv ((M.inclusion n).obj X) =
            (M.inclusion n).obj (targetChoice (M.liftFunctor n) (a n) X),
          b.hom ((M.inclusion n).obj X) ≫ eqToHom e = (M.inclusion n).map g :=
    fun n ↦ (M.functor t M.mem_compressors n).exists_bisection_lift (a n)
      (targetChoice (M.liftFunctor n) (a n))
  choose b hb using hb
  refine ⟨b, fun n ↦ selected (M.liftFunctor n) (a n) (targetChoice (M.liftFunctor n) (a n)),
    fun n ↦ targetChoice (M.liftFunctor n) (a n), ?_,
    fun n X hX ↦ ⟨((mem_selected _ (a n) _ X).mp hX).1, hb n X hX⟩⟩
  obtain ⟨N₀, hN₀⟩ := vanishing_cleanScale (M.unretainedDensity_nonneg t)
    (M.unretained_negligible t M.mem_compressors) (1 / 4) (by norm_num)
  have hT1 := M.unmatched_negligible t M.mem_compressors
  have hT3 := M.badObjects_negligible M.mem_compressors
  have hT5 := hM (1 / 64) (by norm_num) (by norm_num)
  refine Vanishing.squeeze_eventually (((hT1.add hT3).add hT5).const_mul 3) N₀
    fun n hn ↦ ⟨div_nonneg (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (Nat.cast_nonneg _),
      ?_⟩
  have hζ : |cleanScale (M.unretainedDensity t) n| < 1 / 4 := hN₀ n hn
  have hζ' : cleanScale (M.unretainedDensity t) n < 1 / 4 := lt_of_abs_lt hζ
  have hle := M.sum_compl_selected_le a n (η := 1 / 64) (by norm_num) (by norm_num)
    (by linarith)
  exact div_le_div_of_nonneg_right hle (Nat.cast_nonneg _)

end CompressorRelativeData

end CountingEndgame
end GroupApproximation
