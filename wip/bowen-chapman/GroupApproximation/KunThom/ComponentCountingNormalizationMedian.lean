import GroupApproximation.Matching.GlobalVariation

/-!
# Median amplification of one-sided drift

Kun and Thom, *Nonsofic wreath products of residually finite groups*
(arXiv:2608.06222), Lemma 4.4, in the finite vertex form used by the
centralizer-normalization argument.

Let `D` be an expander decomposition of a sofic approximation and `φ` a real
observable on its models, with a chosen median on every ambient component.
The observable is centred at its componentwise median and clamped to `[-M, M]`
(`clampedDeviation`).  Three finite estimates follow.

* `clamped_pinning`: co-area pinning on the ambient components bounds the total
  absolute clamped deviation by the edge variation of the edited graph.
* `sum_abs_clamped_sub_le_of_oneSided`: along a permutation whose drift is
  one-sided off an exceptional set, conservation of mass under a permutation
  (`permutation_conservation_abs`) bounds the absolute variation by twice the
  total rise.  `sum_abs_clamped_sub_le_of_eqOff` treats labels along which the
  observable is invariant off an exceptional set.
* `card_deviation_mul_le`: the vertices at distance at least `M` from their
  componentwise median are counted by the clamped deviation.

`deviation_negligible` and `drop_negligible` assemble these estimates along the
approximation.  The clamp keeps every estimate independent of the range of
`φ`.  Without it, an exceptional set of density `δ / log |Y|` can carry drops of
size `δ` on almost every vertex of an observable with values in
`[0, log |Y|]`, so no one-sided hypothesis of vanishing density could be
amplified.
-/

namespace GroupApproximation
namespace ComponentCountingNormalization

open scoped BigOperators

/-! ### The clamp -/

/-- Clamp a real number to `[-M, M]`. -/
noncomputable def clampTo (M t : ℝ) : ℝ := max (-M) (min M t)

theorem neg_le_clampTo (M t : ℝ) : -M ≤ clampTo M t :=
  le_max_left _ _

theorem clampTo_le {M : ℝ} (hM : 0 ≤ M) (t : ℝ) : clampTo M t ≤ M :=
  max_le (by linarith) (min_le_left _ _)

theorem abs_clampTo_le {M : ℝ} (hM : 0 ≤ M) (t : ℝ) : |clampTo M t| ≤ M :=
  abs_le.mpr ⟨neg_le_clampTo M t, clampTo_le hM t⟩

theorem abs_clampTo_sub_le {M : ℝ} (hM : 0 ≤ M) (s t : ℝ) :
    |clampTo M s - clampTo M t| ≤ 2 * M := by
  have hs₁ := neg_le_clampTo M s
  have hs₂ := clampTo_le hM s
  have ht₁ := neg_le_clampTo M t
  have ht₂ := clampTo_le hM t
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem clampTo_mono (M : ℝ) : Monotone (clampTo M) := by
  intro a b h
  exact max_le_max_left (-M) (le_min (min_le_left _ _) ((min_le_right _ _).trans h))

theorem clampTo_zero {M : ℝ} (hM : 0 ≤ M) : clampTo M 0 = 0 := by
  unfold clampTo
  rw [min_eq_right hM, max_eq_right (by linarith : -M ≤ 0)]

/-- The clamp is one-sided `1`-Lipschitz. -/
theorem clampTo_le_add {M κ a b : ℝ} (hκ : 0 ≤ κ) (h : a ≤ b + κ) :
    clampTo M a ≤ clampTo M b + κ := by
  unfold clampTo
  apply max_le
  · have hb := le_max_left (-M) (min M b)
    linarith
  · rcases le_total M b with hMb | hbM
    · have h₁ : min M a ≤ M := min_le_left _ _
      have h₂ : M ≤ max (-M) (min M b) := by
        rw [min_eq_left hMb]
        exact le_max_right _ _
      linarith
    · have h₁ : min M a ≤ a := min_le_right _ _
      have h₂ : b ≤ max (-M) (min M b) := by
        rw [min_eq_right hbM]
        exact le_max_right _ _
      linarith

/-- A value at distance at least `M` from the origin is clamped to the boundary. -/
theorem abs_clampTo_eq {M t : ℝ} (hM : 0 ≤ M) (ht : M ≤ |t|) : |clampTo M t| = M := by
  unfold clampTo
  rcases le_total 0 t with h₀ | h₀
  · rw [abs_of_nonneg h₀] at ht
    rw [min_eq_left ht, max_eq_right (by linarith : -M ≤ M), abs_of_nonneg hM]
  · rw [abs_of_nonpos h₀] at ht
    rw [min_eq_right (by linarith : t ≤ M), max_eq_left (by linarith : t ≤ -M), abs_neg,
      abs_of_nonneg hM]

/-- Medians transfer along any monotone map. -/
theorem isMedian_comp_monotone {Y : FiniteModel} {f : Y → ℝ} {c : ℝ}
    (hmed : FiniteMultiGraph.IsMedian f c) {g : ℝ → ℝ} (hg : Monotone g) :
    FiniteMultiGraph.IsMedian (fun y ↦ g (f y)) (g c) := by
  constructor
  · have hsub : (Finset.univ.filter fun y ↦ g c < g (f y)) ⊆
        Finset.univ.filter fun y ↦ c < f y := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      by_contra hle
      exact (not_le.mpr hy) (hg (not_lt.mp hle))
    calc 2 * (Finset.univ.filter fun y ↦ g c < g (f y)).card
        ≤ 2 * (Finset.univ.filter fun y ↦ c < f y).card := by
          have hcard := Finset.card_le_card hsub
          omega
      _ ≤ Fintype.card Y := hmed.1
  · have hsub : (Finset.univ.filter fun y ↦ g (f y) < g c) ⊆
        Finset.univ.filter fun y ↦ f y < c := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      by_contra hle
      exact (not_le.mpr hy) (hg (not_lt.mp hle))
    calc 2 * (Finset.univ.filter fun y ↦ g (f y) < g c).card
        ≤ 2 * (Finset.univ.filter fun y ↦ f y < c).card := by
          have hcard := Finset.card_le_card hsub
          omega
      _ ≤ Fintype.card Y := hmed.2

/-! ### The centred clamped observable -/

variable {Y : FiniteModel}

/-- The distinct block containing `y`. -/
def blockIndexOf (Q : BlockStructure Y) (y : Y) : BlockIndex Q :=
  ⟨Q.block y, Q.block_mem_blocksFinset y⟩

theorem blockIndexOf_eq_of_block_eq (Q : BlockStructure Y) {x y : Y}
    (h : Q.block x = Q.block y) : blockIndexOf Q x = blockIndexOf Q y :=
  Subtype.ext h

theorem blockIndexOf_of_mem (Q : BlockStructure Y) (B : BlockIndex Q)
    (x : indexedBlockModel Q B) : blockIndexOf Q (x : Y) = B := by
  have hmem : (x : Y) ∈ Q.block (BlockIndex.representative Q B) := by
    simpa only [BlockIndex.block_representative] using x.2
  exact Subtype.ext ((Q.eq_of_mem _ _ hmem).trans (BlockIndex.block_representative Q B))

/-- The observable centred at its componentwise median and clamped to `[-M, M]`. -/
noncomputable def clampedDeviation (Q : BlockStructure Y) (m : BlockIndex Q → ℝ)
    (φ : Y → ℝ) (M : ℝ) (y : Y) : ℝ :=
  clampTo M (φ y - m (blockIndexOf Q y))

/-- The vertices at distance at least `M` from their componentwise median. -/
noncomputable def deviationSet (Q : BlockStructure Y) (m : BlockIndex Q → ℝ)
    (φ : Y → ℝ) (M : ℝ) : Finset Y :=
  Finset.univ.filter fun y ↦ M ≤ |φ y - m (blockIndexOf Q y)|

/-- The vertices whose image under `p` changes the observable by more than `δ`. -/
noncomputable def dropSet (φ : Y → ℝ) (p : Equiv.Perm Y) (δ : ℝ) : Finset Y :=
  Finset.univ.filter fun y ↦ δ < |φ (p y) - φ y|

/-- On one ambient component the clamped deviation has median `0`. -/
theorem clampedDeviation_isMedian_on_block (Q : BlockStructure Y) (m : BlockIndex Q → ℝ)
    (φ : Y → ℝ) {M : ℝ} (hM : 0 ≤ M) (B : BlockIndex Q)
    (hmed : FiniteMultiGraph.IsMedian (fun x : indexedBlockModel Q B ↦ φ (x : Y)) (m B)) :
    FiniteMultiGraph.IsMedian
      (fun x : indexedBlockModel Q B ↦ clampedDeviation Q m φ M (x : Y)) 0 := by
  have hmono : Monotone fun t : ℝ ↦ clampTo M (t - m B) := by
    intro a b h
    exact clampTo_mono M (by linarith)
  have h : FiniteMultiGraph.IsMedian
      (fun x : indexedBlockModel Q B ↦ clampTo M (φ (x : Y) - m B))
      (clampTo M (m B - m B)) :=
    isMedian_comp_monotone hmed hmono
  rw [sub_self, clampTo_zero hM] at h
  have hfun : (fun x : indexedBlockModel Q B ↦ clampedDeviation Q m φ M (x : Y)) =
      fun x ↦ clampTo M (φ (x : Y) - m B) := by
    funext x
    unfold clampedDeviation
    rw [blockIndexOf_of_mem Q B x]
  rw [hfun]
  exact h

/-- Along a permutation with one-sided drift off `E`, the clamped deviation has
absolute variation at most twice its total rise. -/
theorem sum_abs_clamped_sub_le_of_oneSided (Q : BlockStructure Y) (m : BlockIndex Q → ℝ)
    (φ : Y → ℝ) {M κ : ℝ} (hM : 0 ≤ M) (hκ : 0 ≤ κ) (p : Equiv.Perm Y) (E : Finset Y)
    (hdrift : ∀ y, y ∉ E → φ (p y) ≤ φ y + κ) :
    ∑ y : Y, |clampedDeviation Q m φ M (p y) - clampedDeviation Q m φ M y| ≤
      2 * (κ * Fintype.card Y + 2 * M * ((E ∪ wordCrossing Q p).card : ℝ)) := by
  rw [permutation_conservation_abs p (clampedDeviation Q m φ M),
    permutation_conservation p (clampedDeviation Q m φ M)]
  have hterm : ∀ y : Y,
      max (clampedDeviation Q m φ M (p y) - clampedDeviation Q m φ M y) 0 ≤
        κ + if y ∈ E ∪ wordCrossing Q p then 2 * M else 0 := by
    intro y
    by_cases hy : y ∈ E ∪ wordCrossing Q p
    · rw [if_pos hy]
      have hdiff := abs_clampTo_sub_le hM (φ (p y) - m (blockIndexOf Q (p y)))
        (φ y - m (blockIndexOf Q y))
      have hle : max (clampedDeviation Q m φ M (p y) - clampedDeviation Q m φ M y) 0 ≤
          2 * M := max_le ((le_abs_self _).trans hdiff) (by linarith)
      linarith
    · rw [if_neg hy]
      rw [Finset.mem_union, not_or] at hy
      obtain ⟨hyE, hyW⟩ := hy
      have hblock : Q.block (p y) = Q.block y := by
        by_contra hne
        exact hyW ((mem_wordCrossing Q p y).mpr hne)
      have hstep : clampedDeviation Q m φ M (p y) ≤ clampedDeviation Q m φ M y + κ := by
        unfold clampedDeviation
        rw [blockIndexOf_eq_of_block_eq Q hblock]
        exact clampTo_le_add hκ (by linarith [hdrift y hyE])
      exact max_le (by linarith) (by linarith)
  have hsum : ∑ y : Y, max (clampedDeviation Q m φ M (p y) - clampedDeviation Q m φ M y) 0 ≤
      κ * Fintype.card Y + 2 * M * ((E ∪ wordCrossing Q p).card : ℝ) := by
    calc ∑ y : Y, max (clampedDeviation Q m φ M (p y) - clampedDeviation Q m φ M y) 0
        ≤ ∑ y : Y, (κ + if y ∈ E ∪ wordCrossing Q p then 2 * M else 0) :=
          Finset.sum_le_sum fun y _ ↦ hterm y
      _ = κ * Fintype.card Y + 2 * M * ((E ∪ wordCrossing Q p).card : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Finset.sum_ite_mem,
            Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
          ring
  linarith

/-- Along a permutation that preserves the observable off `E`, the clamped
deviation varies only on `E` and on the crossings of the ambient partition. -/
theorem sum_abs_clamped_sub_le_of_eqOff (Q : BlockStructure Y) (m : BlockIndex Q → ℝ)
    (φ : Y → ℝ) {M : ℝ} (hM : 0 ≤ M) (p : Equiv.Perm Y) (E : Finset Y)
    (hinv : ∀ y, y ∉ E → φ (p y) = φ y) :
    ∑ y : Y, |clampedDeviation Q m φ M (p y) - clampedDeviation Q m φ M y| ≤
      2 * M * ((E ∪ wordCrossing Q p).card : ℝ) := by
  have hterm : ∀ y : Y,
      |clampedDeviation Q m φ M (p y) - clampedDeviation Q m φ M y| ≤
        if y ∈ E ∪ wordCrossing Q p then 2 * M else 0 := by
    intro y
    by_cases hy : y ∈ E ∪ wordCrossing Q p
    · rw [if_pos hy]
      exact abs_clampTo_sub_le hM (φ (p y) - m (blockIndexOf Q (p y)))
        (φ y - m (blockIndexOf Q y))
    · rw [if_neg hy]
      rw [Finset.mem_union, not_or] at hy
      obtain ⟨hyE, hyW⟩ := hy
      have hblock : Q.block (p y) = Q.block y := by
        by_contra hne
        exact hyW ((mem_wordCrossing Q p y).mpr hne)
      have heq : clampedDeviation Q m φ M (p y) = clampedDeviation Q m φ M y := by
        unfold clampedDeviation
        rw [blockIndexOf_eq_of_block_eq Q hblock, hinv y hyE]
      rw [heq, sub_self, abs_zero]
  calc ∑ y : Y, |clampedDeviation Q m φ M (p y) - clampedDeviation Q m φ M y|
      ≤ ∑ y : Y, (if y ∈ E ∪ wordCrossing Q p then 2 * M else 0) :=
        Finset.sum_le_sum fun y _ ↦ hterm y
    _ = 2 * M * ((E ∪ wordCrossing Q p).card : ℝ) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
        ring

/-- Markov's inequality for the clamped deviation. -/
theorem card_deviation_mul_le (Q : BlockStructure Y) (m : BlockIndex Q → ℝ) (φ : Y → ℝ)
    {M : ℝ} (hM : 0 ≤ M) :
    M * ((deviationSet Q m φ M).card : ℝ) ≤ ∑ y : Y, |clampedDeviation Q m φ M y| := by
  calc M * ((deviationSet Q m φ M).card : ℝ)
      = ∑ y ∈ deviationSet Q m φ M, M := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ y ∈ deviationSet Q m φ M, |clampedDeviation Q m φ M y| := by
        apply Finset.sum_le_sum
        intro y hy
        have hy' : M ≤ |φ y - m (blockIndexOf Q y)| := by
          simpa only [deviationSet, Finset.mem_filter, Finset.mem_univ, true_and] using hy
        exact (abs_clampTo_eq hM hy').ge
    _ ≤ ∑ y : Y, |clampedDeviation Q m φ M y| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ ↦ abs_nonneg _)

/-- A permutation changes the observable by more than `2M` only at deviating
vertices, at preimages of deviating vertices, and at crossings. -/
theorem card_drop_le (Q : BlockStructure Y) (m : BlockIndex Q → ℝ) (φ : Y → ℝ)
    (M : ℝ) (p : Equiv.Perm Y) :
    (dropSet φ p (2 * M)).card ≤
      (deviationSet Q m φ M).card + (deviationSet Q m φ M).card +
        (wordCrossing Q p).card := by
  have hpre : (Finset.univ.filter fun y : Y ↦
      M ≤ |φ (p y) - m (blockIndexOf Q (p y))|).card = (deviationSet Q m φ M).card :=
    Finset.card_equiv p fun y ↦ by
      simp only [deviationSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hsub : dropSet φ p (2 * M) ⊆
      (deviationSet Q m φ M ∪
        Finset.univ.filter fun y : Y ↦ M ≤ |φ (p y) - m (blockIndexOf Q (p y))|) ∪
          wordCrossing Q p := by
    intro y hy
    have hy' : 2 * M < |φ (p y) - φ y| := by
      simpa only [dropSet, Finset.mem_filter, Finset.mem_univ, true_and] using hy
    by_contra hnot
    rw [Finset.mem_union, Finset.mem_union, not_or, not_or] at hnot
    obtain ⟨⟨hdy, hpy⟩, hwy⟩ := hnot
    have hblock : Q.block (p y) = Q.block y := by
      by_contra hne
      exact hwy ((mem_wordCrossing Q p y).mpr hne)
    have h₁ : |φ y - m (blockIndexOf Q y)| < M := by
      by_contra h
      exact hdy (by
        simp only [deviationSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact not_lt.mp h)
    have h₂ : |φ (p y) - m (blockIndexOf Q (p y))| < M := by
      by_contra h
      exact hpy (by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact not_lt.mp h)
    rw [blockIndexOf_eq_of_block_eq Q hblock] at h₂
    have h₃ := abs_sub_le (φ (p y)) (m (blockIndexOf Q y)) (φ y)
    rw [abs_sub_comm (m (blockIndexOf Q y)) (φ y)] at h₃
    linarith
  calc (dropSet φ p (2 * M)).card
      ≤ ((deviationSet Q m φ M ∪
          Finset.univ.filter fun y : Y ↦ M ≤ |φ (p y) - m (blockIndexOf Q (p y))|) ∪
            wordCrossing Q p).card := Finset.card_le_card hsub
    _ ≤ (deviationSet Q m φ M ∪
          Finset.univ.filter fun y : Y ↦ M ≤ |φ (p y) - m (blockIndexOf Q (p y))|).card +
            (wordCrossing Q p).card := Finset.card_union_le _ _
    _ ≤ (deviationSet Q m φ M).card +
          (Finset.univ.filter fun y : Y ↦ M ≤ |φ (p y) - m (blockIndexOf Q (p y))|).card +
            (wordCrossing Q p).card := by
        have hunion := Finset.card_union_le (deviationSet Q m φ M)
          (Finset.univ.filter fun y : Y ↦ M ≤ |φ (p y) - m (blockIndexOf Q (p y))|)
        omega
    _ = (deviationSet Q m φ M).card + (deviationSet Q m φ M).card +
          (wordCrossing Q p).card := by
        rw [hpre]

/-! ### Rescaling and edge edits -/

/-- Affine maps scale edge variation by the absolute value of the slope. -/
theorem edgeVariation_mul_add (X : FiniteMultiGraph) (f : X.vertex → ℝ) (a b : ℝ) :
    X.edgeVariation (fun x ↦ a * f x + b) = |a| * X.edgeVariation f := by
  unfold FiniteMultiGraph.edgeVariation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [← abs_mul]
  congr 1
  ring

/-- The affine rescaling of a function bounded by `M` into `[0, 1]`. -/
noncomputable def unitNormalize (M : ℝ) (f : Y → ℝ) (y : Y) : ℝ :=
  1 / (2 * M) * f y + 1 / 2

theorem half_scale {M : ℝ} (hM : 0 < M) : 1 / (2 * M) * M = 1 / 2 := by
  rw [div_mul_eq_mul_div, one_mul, div_eq_iff (by linarith : (0 : ℝ) < 2 * M).ne']
  ring

theorem unitNormalize_nonneg {M : ℝ} (hM : 0 < M) {f : Y → ℝ} (hf : ∀ y, |f y| ≤ M)
    (y : Y) : 0 ≤ unitNormalize M f y := by
  have hk : 0 ≤ 1 / (2 * M) := (one_div_pos.mpr (by linarith)).le
  have hlow : -M ≤ f y := (abs_le.mp (hf y)).1
  have h₁ := mul_le_mul_of_nonneg_left hlow hk
  rw [mul_neg, half_scale hM] at h₁
  unfold unitNormalize
  linarith

theorem unitNormalize_le_one {M : ℝ} (hM : 0 < M) {f : Y → ℝ} (hf : ∀ y, |f y| ≤ M)
    (y : Y) : unitNormalize M f y ≤ 1 := by
  have hk : 0 ≤ 1 / (2 * M) := (one_div_pos.mpr (by linarith)).le
  have hhigh : f y ≤ M := (abs_le.mp (hf y)).2
  have h₁ := mul_le_mul_of_nonneg_left hhigh hk
  rw [half_scale hM] at h₁
  unfold unitNormalize
  linarith

variable {G : Type} [Group G] {S : SoficApproximation G} {T : Finset G}

/-- Edge edits change the variation of a function bounded by `M` by at most
`2M` per unmatched occurrence. -/
theorem clamped_modelVariation_le (D : ExpanderDecomposition S T) (n : ℕ)
    (f : S.model n → ℝ) {M : ℝ} (hM : 0 < M) (hf : ∀ y, |f y| ≤ M) :
    (D.modelGraph n).edgeVariation f ≤
      ∑ t : T, ∑ x : S.model n, |f (S.map n t.1 x) - f x| +
        2 * M * ((D.editWitness n).unmatchedCount : ℝ) := by
  have h2M : (0 : ℝ) < 2 * M := by linarith
  have hk : 2 * M * (1 / (2 * M)) = 1 := mul_one_div_cancel h2M.ne'
  have hrec : (fun y ↦ 2 * M * unitNormalize M f y + -M) = f := by
    funext y
    unfold unitNormalize
    rw [mul_add, ← mul_assoc, hk, one_mul]
    ring
  have hmodel : (D.modelGraph n).edgeVariation f =
      2 * M * (D.modelGraph n).edgeVariation (unitNormalize M f) := by
    conv_lhs => rw [← hrec]
    rw [edgeVariation_mul_add, abs_of_pos h2M]
  have hgen : (generatorGraph (S.model n) T (S.map n)).edgeVariation f =
      2 * M * (generatorGraph (S.model n) T (S.map n)).edgeVariation (unitNormalize M f) := by
    conv_lhs => rw [← hrec]
    rw [edgeVariation_mul_add, abs_of_pos h2M]
  have hedit := (D.editWitness n).targetVariation_le_unmatchedCount
    (unitNormalize M f) (unitNormalize M f) (fun _ ↦ rfl)
    (unitNormalize_nonneg hM hf) (unitNormalize_le_one hM hf)
  have hlabels := generatorGraph_edgeVariation_le T (S.map n) f
  have hscaled : 2 * M * (D.modelGraph n).edgeVariation (unitNormalize M f) ≤
      2 * M * ((generatorGraph (S.model n) T (S.map n)).edgeVariation (unitNormalize M f) +
        ((D.editWitness n).unmatchedCount : ℝ)) :=
    mul_le_mul_of_nonneg_left hedit h2M.le
  rw [hmodel]
  linarith

/-! ### Pinning and the asymptotic statements -/

/-- Co-area pinning of the clamped deviation on the ambient components. -/
theorem clamped_pinning (D : ExpanderDecomposition S T) (n : ℕ)
    (m : D.componentIndex n → ℝ) (φ : S.model n → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hmed : ∀ B : D.componentIndex n, FiniteMultiGraph.IsMedian
      (fun x : indexedBlockModel (D.blocks n) B ↦ φ (x : S.model n)) (m B)) :
    D.cheeger * ∑ y : S.model n, |clampedDeviation (D.blocks n) m φ M y| ≤
      (D.modelGraph n).edgeVariation (clampedDeviation (D.blocks n) m φ M) := by
  have hmul : D.cheeger * ∑ B : D.componentIndex n,
        ∑ x : indexedBlockModel (D.blocks n) B,
          |clampedDeviation (D.blocks n) m φ M (x : S.model n)| ≤
      ∑ B : D.componentIndex n, (D.indexedComponentGraph n B).edgeVariation
        (fun x ↦ clampedDeviation (D.blocks n) m φ M (x : S.model n)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro B _
    have h := FiniteMultiGraph.coarea_mul (D.indexedComponentGraph n B)
      (D.indexedComponentGraph_expands n B)
      (fun x ↦ clampedDeviation (D.blocks n) m φ M (x : S.model n)) 0
      (clampedDeviation_isMedian_on_block (D.blocks n) m φ hM B (hmed B))
    simpa only [sub_zero] using h
  rw [← D.sum_indexedComponent_edgeVariation,
    ← BlockIndex.sum_sum (D.blocks n) (fun y ↦ |clampedDeviation (D.blocks n) m φ M y|)]
  exact hmul

/-- **Median amplification**, deviation form.  If every label of the ambient
generator set moves the clamped deviation by a negligible total amount, then
the vertices at distance at least `M` from their componentwise median are
negligible. -/
theorem deviation_negligible (D : ExpanderDecomposition S T)
    (m : ∀ n, D.componentIndex n → ℝ) (φ : ∀ n, S.model n → ℝ)
    (hmed : ∀ n (B : D.componentIndex n), FiniteMultiGraph.IsMedian
      (fun x : indexedBlockModel (D.blocks n) B ↦ φ n (x : S.model n)) (m n B))
    {M : ℝ} (hM : 0 < M)
    (hlabel : ∀ t ∈ T, Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ∑ x : S.model n, |clampedDeviation (D.blocks n) (m n) (φ n) M (S.map n t x) -
        clampedDeviation (D.blocks n) (m n) (φ n) M x|) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ((deviationSet (D.blocks n) (m n) (φ n) M).card : ℝ) := by
  have hN : ∀ n, (0 : ℝ) ≤ Fintype.card (S.model n) := fun n ↦ by positivity
  have hlabels : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ∑ t ∈ (Finset.univ : Finset T), ∑ x : S.model n,
        |clampedDeviation (D.blocks n) (m n) (φ n) M (S.map n t.1 x) -
          clampedDeviation (D.blocks n) (m n) (φ n) M x| :=
    Negligible.sum Finset.univ _ fun t _ ↦ hlabel t.1 t.2
  have hvar : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      (D.modelGraph n).edgeVariation (clampedDeviation (D.blocks n) (m n) (φ n) M) := by
    refine Negligible.mono_nonneg hN (fun n ↦ ?_) (fun n ↦ ?_)
      (hlabels.add (Negligible.const_mul (2 * M) D.unmatched_negligible))
    · unfold FiniteMultiGraph.edgeVariation
      positivity
    · exact clamped_modelVariation_le D n _ hM
        (fun y ↦ abs_clampTo_le hM.le (φ n y - m n (blockIndexOf (D.blocks n) y)))
  have hdev : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ∑ y : S.model n, |clampedDeviation (D.blocks n) (m n) (φ n) M y| := by
    refine Negligible.mono_nonneg hN (fun n ↦ by positivity) (fun n ↦ ?_)
      (Negligible.const_mul (1 / D.cheeger) hvar)
    have hpin := clamped_pinning D n (m n) (φ n) hM.le (hmed n)
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ D.cheeger_pos]
    linarith
  refine Negligible.mono_nonneg hN (fun n ↦ by positivity) (fun n ↦ ?_)
    (Negligible.const_mul (1 / M) hdev)
  have hmarkov := card_deviation_mul_le (D.blocks n) (m n) (φ n) hM.le
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hM]
  linarith

/-- **Median amplification**, drop form.  A permutation that rarely crosses the
ambient components changes a median-concentrated observable by more than `2M`
only on a negligible set. -/
theorem drop_negligible (D : ExpanderDecomposition S T)
    (m : ∀ n, D.componentIndex n → ℝ) (φ : ∀ n, S.model n → ℝ) (M : ℝ)
    (p : ∀ n, Equiv.Perm (S.model n))
    (hdev : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ((deviationSet (D.blocks n) (m n) (φ n) M).card : ℝ))
    (hcross : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ((wordCrossing (D.blocks n) (p n)).card : ℝ)) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ((dropSet (φ n) (p n) (2 * M)).card : ℝ) := by
  have hN : ∀ n, (0 : ℝ) ≤ Fintype.card (S.model n) := fun n ↦ by positivity
  refine Negligible.mono_nonneg hN (fun n ↦ by positivity) (fun n ↦ ?_)
    ((hdev.add hdev).add hcross)
  exact_mod_cast card_drop_le (D.blocks n) (m n) (φ n) M (p n)

end ComponentCountingNormalization
end GroupApproximation
