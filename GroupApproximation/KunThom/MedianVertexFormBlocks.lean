import GroupApproximation.KunThom.MedianVertexFormLocal
import GroupApproximation.KunThom.BisectionActualDefect
import GroupApproximation.KunThom.ComponentCountingRelativeFunctorBridges
import GroupApproximation.KunThom.NormalizationFromCriterion

/-!
# Kun–Thom Lemma 4.4 for embedded cluster blocks

This file states the vertex form of Kun and Thom's one-sided median lemma
(arXiv:2608.06222v3, Lemma 4.4) in the shape consumed by the counting endgame of
their proof of Theorem 4.1.

The objects at stage `n` form a finite type `index n`, embedded as disjoint
blocks `E n : BlockEmbedding (A.model n) (index n)`.  An object weighs
`|E.model i|`, and a family of objects is measured by the sum of the weights of
its members against `|A.model n|`.  The observable of the objects is a natural
function `f n ≥ 1`, such as orbit sizes or isotropy orders of the cluster
groupoid.  It is read at a vertex through its block (`blockObject`), and is `1`
on uncovered vertices.  The ambient decomposition `DG` is an arbitrary expander
decomposition of the sofic approximation `A` for a symmetric generating set `T`.

The inputs are, for every compressor `q` of a compression setup `C`:

* the one-sided inequality `f (π q n i) ≤ (1 + κ q n) f i` for `i ∈ Dom q n` off
  a family `Bad q n` of negligible weight, with `κ q` vanishing;
* negligible weight outside `Dom q n`;
* negligible missing source mass of the bridges realized by the compressor
  permutation from each `i ∈ Dom q n` to its match `π q n i`.

In addition the uncovered vertices must be negligible, and so must the missing
source mass of the bridges realized by every embedded generator of `Γ` from each
block to itself.

* `blockObject`, with `blockObject_embed` and
  `exists_embed_of_blockObject_eq_some`: the block through a vertex.
* `card_objectVertices_image_some_le`, `sum_card_le_card_objectVertices_image_some`,
  `card_outsideVertices_image_some_le`, `card_matchLeak_image_some_le` and
  `card_blockObject_change_le`: the vertex exceptional sets are at most the
  object weights, the uncovered mass and the missing bridge mass.
* `logCut_le_add_of_le_mul` and `sq_mul_le_of_abs_logCut_sub_le`: multiplicative
  one-sided inequalities give additive drift of the logarithmic observable, and
  bounded logarithmic changes give the squared ratio bounds.
* `blockInvariantLabel_negligible` and `blockCompressorLabel_negligible`: the
  label estimates, which `sum_abs_sub_negligible_of_closure` extends from the
  ambient generators of `C` to every element of `T`.
* `blockRatio_negligible`: for every `η` with `0 < η` and `2η < 1`, the matched
  objects with `¬ ((1 - 2η)² f (π i) ≤ (1 + 2η)² f i ∧ (1 - 2η)² f i ≤ (1 + 2η)² f (π i))`
  have negligible total weight.
-/

namespace GroupApproximation
namespace MedianVertexForm

open scoped BigOperators
open ComponentCountingNormalization BlockPatching

/-! ### The block through a vertex -/

section Blocks

variable {Y : FiniteModel} {I : Type*}

/-- The block through a vertex, and `none` on uncovered vertices. -/
noncomputable def blockObject (E : BlockEmbedding Y I) (y : Y) : Option I := by
  classical
  exact if h : ∃ i, ∃ x : E.model i, E.embed i x = y then some (Classical.choose h) else none

theorem blockObject_embed (E : BlockEmbedding Y I) (i : I) (x : E.model i) :
    blockObject E (E.embed i x) = some i := by
  have h : ∃ j, ∃ z : E.model j, E.embed j z = E.embed i x := ⟨i, x, rfl⟩
  rw [blockObject, dif_pos h]
  obtain ⟨z, hz⟩ := Classical.choose_spec h
  exact congrArg some (E.embed_disjoint _ i z x hz)

theorem exists_embed_of_blockObject_eq_some (E : BlockEmbedding Y I) {y : Y} {i : I}
    (h : blockObject E y = some i) : ∃ x : E.model i, E.embed i x = y := by
  classical
  by_cases hy : ∃ j, ∃ z : E.model j, E.embed j z = y
  · rw [blockObject, dif_pos hy] at h
    have hi : Classical.choose hy = i := Option.some.inj h
    subst hi
    exact Classical.choose_spec hy
  · rw [blockObject, dif_neg hy] at h
    simp at h

theorem mem_uncovered_of_blockObject_eq_none (E : BlockEmbedding Y I) {y : Y}
    (h : blockObject E y = none) : y ∈ E.uncovered := by
  rw [E.mem_uncovered]
  intro i x hxy
  rw [← hxy, blockObject_embed] at h
  simp at h

/-- The missing source mass of a bridge is the number of block points the
permutation carries outside the target block. -/
theorem card_sdiff_bridgeSource (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I) :
    (Finset.univ \ E.bridgeSource q C D).card = (E.bridge q C D).sourceDefect := by
  have h := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (E.model C))
    (E.bridgeSource q C D)
  rw [Finset.univ_inter, Finset.card_univ] at h
  show (Finset.univ \ E.bridgeSource q C D).card =
    Fintype.card (E.model C) - (E.bridgeSource q C D).card
  omega

theorem card_objectVertices_image_some_le [DecidableEq I] (E : BlockEmbedding Y I)
    (J : Finset I) :
    (objectVertices (blockObject E) (J.image some)).card ≤
      ∑ i ∈ J, Fintype.card (E.model i) := by
  have hsub : objectVertices (blockObject E) (J.image some) ⊆
      J.biUnion fun i ↦ (Finset.univ : Finset (E.model i)).image (E.embed i) := by
    intro y hy
    rw [mem_objectVertices, Finset.mem_image] at hy
    obtain ⟨i, hi, hiy⟩ := hy
    obtain ⟨x, hx⟩ := exists_embed_of_blockObject_eq_some E hiy.symm
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩⟩
  calc (objectVertices (blockObject E) (J.image some)).card
      ≤ (J.biUnion fun i ↦ (Finset.univ : Finset (E.model i)).image (E.embed i)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ i ∈ J, ((Finset.univ : Finset (E.model i)).image (E.embed i)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ i ∈ J, Fintype.card (E.model i) :=
        Finset.sum_le_sum fun i _ ↦ Finset.card_image_le.trans (Finset.card_univ).le

theorem sum_card_le_card_objectVertices_image_some [DecidableEq I] (E : BlockEmbedding Y I)
    (J : Finset I) :
    ∑ i ∈ J, Fintype.card (E.model i) ≤
      (objectVertices (blockObject E) (J.image some)).card := by
  have hsub : (J.biUnion fun i ↦ (Finset.univ : Finset (E.model i)).image (E.embed i)) ⊆
      objectVertices (blockObject E) (J.image some) := by
    intro y hy
    obtain ⟨i, hi, hy'⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy'
    rw [mem_objectVertices, blockObject_embed]
    exact Finset.mem_image_of_mem some hi
  have hdisj : (J : Set I).PairwiseDisjoint
      fun i ↦ (Finset.univ : Finset (E.model i)).image (E.embed i) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro y hyi hyj
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hyi
    obtain ⟨z, _, hz⟩ := Finset.mem_image.mp hyj
    exact hij (E.embed_disjoint j i z x hz).symm
  calc ∑ i ∈ J, Fintype.card (E.model i)
      = ∑ i ∈ J, ((Finset.univ : Finset (E.model i)).image (E.embed i)).card := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.card_image_of_injective _ (E.embed_injective i), Finset.card_univ]
    _ = (J.biUnion fun i ↦ (Finset.univ : Finset (E.model i)).image (E.embed i)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (objectVertices (blockObject E) (J.image some)).card := Finset.card_le_card hsub

theorem card_outsideVertices_image_some_le [Fintype I] [DecidableEq I]
    (E : BlockEmbedding Y I) (Dom : Finset I) :
    (outsideVertices (blockObject E) (Dom.image some)).card ≤
      E.uncovered.card + ∑ i ∈ Finset.univ \ Dom, Fintype.card (E.model i) := by
  have hsub : outsideVertices (blockObject E) (Dom.image some) ⊆
      E.uncovered ∪ objectVertices (blockObject E) ((Finset.univ \ Dom).image some) := by
    intro y hy
    rw [mem_outsideVertices] at hy
    rw [Finset.mem_union]
    rcases hb : blockObject E y with _ | i
    · exact Or.inl (mem_uncovered_of_blockObject_eq_none E hb)
    · right
      rw [mem_objectVertices, hb]
      rw [hb] at hy
      refine Finset.mem_image_of_mem some (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, ?_⟩)
      intro hi
      exact hy (Finset.mem_image_of_mem some hi)
  calc (outsideVertices (blockObject E) (Dom.image some)).card
      ≤ (E.uncovered ∪ objectVertices (blockObject E) ((Finset.univ \ Dom).image some)).card :=
        Finset.card_le_card hsub
    _ ≤ E.uncovered.card +
          (objectVertices (blockObject E) ((Finset.univ \ Dom).image some)).card :=
        Finset.card_union_le _ _
    _ ≤ E.uncovered.card + ∑ i ∈ Finset.univ \ Dom, Fintype.card (E.model i) := by
        have h := card_objectVertices_image_some_le E (Finset.univ \ Dom)
        omega

theorem card_matchLeak_image_some_le [DecidableEq I] (E : BlockEmbedding Y I)
    (p : Equiv.Perm Y) (π : I → I) (Dom : Finset I) :
    (matchLeak (blockObject E) p (Option.map π) (Dom.image some)).card ≤
      ∑ i ∈ Dom, (E.bridge p i (π i)).sourceDefect := by
  have hsub : matchLeak (blockObject E) p (Option.map π) (Dom.image some) ⊆
      Dom.biUnion fun i ↦ (Finset.univ \ E.bridgeSource p i (π i)).image (E.embed i) := by
    intro y hy
    rw [mem_matchLeak, Finset.mem_image] at hy
    obtain ⟨⟨i, hi, hiy⟩, hleak⟩ := hy
    obtain ⟨x, rfl⟩ := exists_embed_of_blockObject_eq_some E hiy.symm
    refine Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image.mpr ⟨x, ?_, rfl⟩⟩
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, fun hx ↦ hleak ?_⟩
    obtain ⟨z, hz⟩ := (E.mem_bridgeSource p i (π i) x).mp hx
    have h₁ : blockObject E (p (E.embed i x)) = some (π i) := by
      rw [← hz]
      exact blockObject_embed E (π i) z
    exact h₁.trans (congrArg (Option.map π) (blockObject_embed E i x)).symm
  calc (matchLeak (blockObject E) p (Option.map π) (Dom.image some)).card
      ≤ (Dom.biUnion fun i ↦
          (Finset.univ \ E.bridgeSource p i (π i)).image (E.embed i)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Dom, ((Finset.univ \ E.bridgeSource p i (π i)).image (E.embed i)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ i ∈ Dom, (E.bridge p i (π i)).sourceDefect :=
        Finset.sum_le_sum fun i _ ↦
          Finset.card_image_le.trans (card_sdiff_bridgeSource E p i (π i)).le

theorem card_blockObject_change_le [Fintype I] [DecidableEq I] (E : BlockEmbedding Y I)
    (p : Equiv.Perm Y) :
    (Finset.univ.filter fun y ↦ blockObject E (p y) ≠ blockObject E y).card ≤
      E.uncovered.card + ∑ i, (E.bridge p i i).sourceDefect := by
  have hsub : (Finset.univ.filter fun y ↦ blockObject E (p y) ≠ blockObject E y) ⊆
      E.uncovered ∪
        Finset.univ.biUnion fun i ↦ (Finset.univ \ E.bridgeSource p i i).image (E.embed i) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    rw [Finset.mem_union]
    rcases hb : blockObject E y with _ | i
    · exact Or.inl (mem_uncovered_of_blockObject_eq_none E hb)
    · right
      obtain ⟨x, rfl⟩ := exists_embed_of_blockObject_eq_some E hb
      refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨x, ?_, rfl⟩⟩
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, fun hx ↦ hy.2 ?_⟩
      obtain ⟨z, hz⟩ := (E.mem_bridgeSource p i i x).mp hx
      rw [← hz, blockObject_embed, blockObject_embed]
  have hbiUnion : (Finset.univ.biUnion fun i ↦
      (Finset.univ \ E.bridgeSource p i i).image (E.embed i)).card ≤
        ∑ i, (E.bridge p i i).sourceDefect :=
    Finset.card_biUnion_le.trans
      (Finset.sum_le_sum fun i _ ↦ Finset.card_image_le.trans (card_sdiff_bridgeSource E p i i).le)
  have hunion := Finset.card_union_le E.uncovered
    (Finset.univ.biUnion fun i ↦ (Finset.univ \ E.bridgeSource p i i).image (E.embed i))
  have hcard := Finset.card_le_card hsub
  omega

end Blocks

/-! ### Multiplicative inequalities and squared ratios -/

/-- A natural observable of the objects, extended by `1` on uncovered vertices. -/
def optionObservable {I : Type*} (f : I → ℕ) (o : Option I) : ℕ :=
  o.elim 1 f

/-- **Multiplicative to additive drift.**  If `a ≤ (1 + κ) b` with `0 ≤ κ`, the
logarithmic observable rises from `b` to `a` by at most `κ`. -/
theorem logCut_le_add_of_le_mul {a b : ℕ} {κ : ℝ} (hκ : 0 ≤ κ) (h : (a : ℝ) ≤ (1 + κ) * b) :
    Real.log (max (a : ℝ) 1) ≤ Real.log (max (b : ℝ) 1) + κ := by
  have hy1 : (1 : ℝ) ≤ max (b : ℝ) 1 := le_max_right _ _
  have hxpos : (0 : ℝ) < max (a : ℝ) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hypos : (0 : ℝ) < max (b : ℝ) 1 := lt_of_lt_of_le one_pos hy1
  have hκ₁ : (0 : ℝ) ≤ 1 + κ := by linarith
  have hmul : max (a : ℝ) 1 ≤ (1 + κ) * max (b : ℝ) 1 := by
    apply max_le
    · have hscaled := mul_le_mul_of_nonneg_left (le_max_left (b : ℝ) 1) hκ₁
      linarith
    · have hscaled := mul_le_mul_of_nonneg_left hy1 hκ₁
      linarith
  have hratio : max (a : ℝ) 1 / max (b : ℝ) 1 - 1 ≤ κ := by
    rw [div_sub_one hypos.ne', div_le_iff₀ hypos]
    linarith
  have hlog : Real.log (max (a : ℝ) 1) - Real.log (max (b : ℝ) 1) ≤
      max (a : ℝ) 1 / max (b : ℝ) 1 - 1 := by
    rw [← Real.log_div hxpos.ne' hypos.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hxpos hypos)
  linarith

/-- **Squared ratio bound.**  A logarithmic change of at most
`2 (log (1 + 2η) - log (1 - 2η))` between positive natural observables gives
`(1 - 2η)² a ≤ (1 + 2η)² b`. -/
theorem sq_mul_le_of_abs_logCut_sub_le {a b : ℕ} {η : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hη₂ : 2 * η < 1) (hη : 0 < η)
    (h : |Real.log (max (a : ℝ) 1) - Real.log (max (b : ℝ) 1)| ≤
      2 * (Real.log (1 + 2 * η) - Real.log (1 - 2 * η))) :
    (1 - 2 * η) ^ 2 * (a : ℝ) ≤ (1 + 2 * η) ^ 2 * b := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  rw [max_eq_left ha', max_eq_left hb'] at h
  have hapos : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha'
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le one_pos hb'
  have hm : (0 : ℝ) < 1 - 2 * η := by linarith
  have hp : (0 : ℝ) < 1 + 2 * η := by linarith
  have h₁ := (abs_le.mp h).2
  have hlog : Real.log ((1 - 2 * η) ^ 2 * (a : ℝ)) ≤ Real.log ((1 + 2 * η) ^ 2 * (b : ℝ)) := by
    rw [show (1 - 2 * η) ^ 2 * (a : ℝ) = (1 - 2 * η) * ((1 - 2 * η) * a) by ring,
      show (1 + 2 * η) ^ 2 * (b : ℝ) = (1 + 2 * η) * ((1 + 2 * η) * b) by ring,
      Real.log_mul hm.ne' (mul_pos hm hapos).ne', Real.log_mul hm.ne' hapos.ne',
      Real.log_mul hp.ne' (mul_pos hp hbpos).ne', Real.log_mul hp.ne' hbpos.ne']
    linarith
  exact (Real.log_le_log_iff (mul_pos (pow_pos hm 2) hapos)
    (mul_pos (pow_pos hp 2) hbpos)).mp hlog

/-! ### Label estimates and the endgame form -/

section Asymptotic

variable {G Γ J : Type} [Group G] [Group Γ] [Group J]

/-- The clamped label variation of the logarithmic observable of the blocks,
centred at its componentwise median on the ambient components. -/
noncomputable def blockLabelVariation (A : SoficApproximation G) {T : Finset G}
    (DG : ExpanderDecomposition A T) {index : ℕ → Type}
    (E : ∀ n, BlockEmbedding (A.model n) (index n)) (f : ∀ n, index n → ℕ) (M : ℝ) (g : G)
    (n : ℕ) : ℝ :=
  ∑ x : A.model n,
    |clampedDeviation (DG.blocks n)
        (logMedian DG (fun n ↦ blockObject (E n)) (fun n ↦ optionObservable (f n)) n)
        (fun y ↦ logObservable (optionObservable (f n)) (blockObject (E n) y)) M
        (A.map n g x) -
      clampedDeviation (DG.blocks n)
        (logMedian DG (fun n ↦ blockObject (E n)) (fun n ↦ optionObservable (f n)) n)
        (fun y ↦ logObservable (optionObservable (f n)) (blockObject (E n) y)) M x|

/-- A label that carries almost every block into itself moves the clamped
logarithmic observable by a negligible total amount. -/
theorem blockInvariantLabel_negligible (A : SoficApproximation G) {T : Finset G}
    (DG : ExpanderDecomposition A T) (hTsymm : ∀ g ∈ T, g⁻¹ ∈ T)
    (hTgen : Subgroup.closure (T : Set G) = ⊤)
    {index : ℕ → Type} [∀ n, Fintype (index n)] [∀ n, DecidableEq (index n)]
    (E : ∀ n, BlockEmbedding (A.model n) (index n)) (f : ∀ n, index n → ℕ) {M : ℝ}
    (hM : 0 ≤ M)
    (huncov : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ((E n).uncovered.card : ℝ))
    (g : G)
    (hg : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ i, (((E n).bridge (A.map n g) i i).sourceDefect : ℝ)) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) (blockLabelVariation A DG E f M g) := by
  have hN : ∀ n, (0 : ℝ) ≤ Fintype.card (A.model n) := fun n ↦ Nat.cast_nonneg _
  have hE : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ((Finset.univ.filter fun y ↦
        blockObject (E n) (A.map n g y) ≠ blockObject (E n) y).card : ℝ) := by
    refine Negligible.mono_nonneg hN (fun n ↦ Nat.cast_nonneg _) (fun n ↦ ?_) (huncov.add hg)
    have h := card_blockObject_change_le (E n) (A.map n g)
    exact_mod_cast h
  have hinv : ∀ n (y : A.model n),
      y ∉ (Finset.univ.filter fun y ↦ blockObject (E n) (A.map n g y) ≠ blockObject (E n) y) →
      logObservable (optionObservable (f n)) (blockObject (E n) (A.map n g y)) =
        logObservable (optionObservable (f n)) (blockObject (E n) y) := by
    intro n y hy
    have heq : blockObject (E n) (A.map n g y) = blockObject (E n) y := by
      by_contra hne
      exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hne⟩)
    rw [heq]
  exact clampedLabel_negligible_of_eqOff DG
    (logMedian DG (fun n ↦ blockObject (E n)) fun n ↦ optionObservable (f n))
    (fun n y ↦ logObservable (optionObservable (f n)) (blockObject (E n) y)) hM g
    (fun n ↦ Finset.univ.filter fun y ↦ blockObject (E n) (A.map n g y) ≠ blockObject (E n) y)
    hE hinv (DG.all_almost_invariant hTsymm hTgen g)

/-- A compressor with one-sided object inequalities off negligible exceptional
families moves the clamped logarithmic observable by a negligible total amount. -/
theorem blockCompressorLabel_negligible (A : SoficApproximation G) {T : Finset G}
    (DG : ExpanderDecomposition A T) (hTsymm : ∀ g ∈ T, g⁻¹ ∈ T)
    (hTgen : Subgroup.closure (T : Set G) = ⊤)
    {index : ℕ → Type} [∀ n, Fintype (index n)] [∀ n, DecidableEq (index n)]
    (E : ∀ n, BlockEmbedding (A.model n) (index n)) (f : ∀ n, index n → ℕ) {M : ℝ}
    (hM : 0 ≤ M)
    (huncov : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ((E n).uncovered.card : ℝ))
    (q : G) (π : ∀ n, index n → index n) (Dom Bad : ∀ n, Finset (index n))
    (κ : ℕ → ℝ) (hκ : ∀ n, 0 ≤ κ n) (hκv : Vanishing κ)
    (hone : ∀ n, ∀ i ∈ Dom n, i ∉ Bad n → (f n (π n i) : ℝ) ≤ (1 + κ n) * f n i)
    (hbad : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ i ∈ Bad n, (Fintype.card ((E n).model i) : ℝ))
    (hout : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ i ∈ Finset.univ \ Dom n, (Fintype.card ((E n).model i) : ℝ))
    (hmiss : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ i ∈ Dom n, (((E n).bridge (A.map n q) i (π n i)).sourceDefect : ℝ)) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) (blockLabelVariation A DG E f M q) := by
  have hN : ∀ n, (0 : ℝ) ≤ Fintype.card (A.model n) := fun n ↦ Nat.cast_nonneg _
  have hE : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ((vertexExceptional (blockObject (E n)) (A.map n q) (Option.map (π n))
        ((Dom n).image some) ((Bad n).image some)).card : ℝ) := by
    refine Negligible.mono_nonneg hN (fun n ↦ Nat.cast_nonneg _) (fun n ↦ ?_)
      (((huncov.add hout).add hbad).add hmiss)
    have h₁ := card_vertexExceptional_le (blockObject (E n)) (A.map n q) (Option.map (π n))
      ((Dom n).image some) ((Bad n).image some)
    have h₂ := card_outsideVertices_image_some_le (E n) (Dom n)
    have h₃ := card_objectVertices_image_some_le (E n) (Bad n)
    have h₄ := card_matchLeak_image_some_le (E n) (A.map n q) (π n) (Dom n)
    have hsum : (vertexExceptional (blockObject (E n)) (A.map n q) (Option.map (π n))
        ((Dom n).image some) ((Bad n).image some)).card ≤
        (E n).uncovered.card + ∑ i ∈ Finset.univ \ Dom n, Fintype.card ((E n).model i) +
          ∑ i ∈ Bad n, Fintype.card ((E n).model i) +
          ∑ i ∈ Dom n, ((E n).bridge (A.map n q) i (π n i)).sourceDefect := by
      omega
    exact_mod_cast hsum
  have hdrift : ∀ n (y : A.model n),
      y ∉ vertexExceptional (blockObject (E n)) (A.map n q) (Option.map (π n))
        ((Dom n).image some) ((Bad n).image some) →
      logObservable (optionObservable (f n)) (blockObject (E n) (A.map n q y)) ≤
        logObservable (optionObservable (f n)) (blockObject (E n) y) + κ n := by
    intro n y hy
    refine drift_of_not_mem_vertexExceptional (blockObject (E n)) (A.map n q) (Option.map (π n))
      ((Dom n).image some) ((Bad n).image some) (logObservable (optionObservable (f n))) (κ n)
      ?_ y hy
    intro o ho hbo
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ho
    have hbi : i ∉ Bad n := fun hb ↦ hbo (Finset.mem_image_of_mem some hb)
    exact logCut_le_add_of_le_mul (hκ n) (hone n i hi hbi)
  exact clampedLabel_negligible_of_oneSided DG
    (logMedian DG (fun n ↦ blockObject (E n)) fun n ↦ optionObservable (f n))
    (fun n y ↦ logObservable (optionObservable (f n)) (blockObject (E n) y)) hM κ hκ hκv q
    (fun n ↦ vertexExceptional (blockObject (E n)) (A.map n q) (Option.map (π n))
      ((Dom n).image some) ((Bad n).image some))
    hE hdrift (DG.all_almost_invariant hTsymm hTgen q)

/-- **Kun–Thom Lemma 4.4, endgame form.**  For a compression setup `C`, an ambient
expander decomposition `DG` of `A` for a symmetric generating set `T`, embedded
blocks `E n` carrying a natural observable `f n ≥ 1`, and, for every compressor,
one-sided object inequalities with negligible exceptional weight, negligible
weight outside the matching domain and negligible missing bridge mass, the
matched objects whose observables are not within the squared factor
`((1 + 2η) / (1 - 2η))²` of each other have negligible total weight. -/
theorem blockRatio_negligible (C : CompressionSetup G Γ J) (A : SoficApproximation G)
    {T : Finset G} (DG : ExpanderDecomposition A T) (hTsymm : ∀ g ∈ T, g⁻¹ ∈ T)
    (hTgen : Subgroup.closure (T : Set G) = ⊤)
    {index : ℕ → Type} [∀ n, Fintype (index n)] [∀ n, DecidableEq (index n)]
    (E : ∀ n, BlockEmbedding (A.model n) (index n))
    (f : ∀ n, index n → ℕ) (hf : ∀ n i, 1 ≤ f n i)
    (huncov : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ((E n).uncovered.card : ℝ))
    (hΓ : ∀ s ∈ C.generatorsΓ, Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ i, (((E n).bridge (A.map n (C.embedΓ s)) i i).sourceDefect : ℝ))
    (π : G → ∀ n, index n → index n) (Dom Bad : G → ∀ n, Finset (index n))
    (κ : G → ℕ → ℝ) (hκ : ∀ q ∈ C.compressors, ∀ n, 0 ≤ κ q n)
    (hκv : ∀ q ∈ C.compressors, Vanishing (κ q))
    (hone : ∀ q ∈ C.compressors, ∀ n, ∀ i ∈ Dom q n, i ∉ Bad q n →
      (f n (π q n i) : ℝ) ≤ (1 + κ q n) * f n i)
    (hbad : ∀ q ∈ C.compressors, Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ i ∈ Bad q n, (Fintype.card ((E n).model i) : ℝ))
    (hout : ∀ q ∈ C.compressors, Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ i ∈ Finset.univ \ Dom q n, (Fintype.card ((E n).model i) : ℝ))
    (hmiss : ∀ q ∈ C.compressors, Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ i ∈ Dom q n, (((E n).bridge (A.map n q) i (π q n i)).sourceDefect : ℝ))
    {η : ℝ} (hη : 0 < η) (hη₂ : 2 * η < 1) (t : G) (ht : t ∈ C.compressors) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ i ∈ (Dom t n).filter (fun i ↦
          ¬ ((1 - 2 * η) ^ 2 * (f n (π t n i) : ℝ) ≤ (1 + 2 * η) ^ 2 * f n i ∧
            (1 - 2 * η) ^ 2 * (f n i : ℝ) ≤ (1 + 2 * η) ^ 2 * f n (π t n i))),
        (Fintype.card ((E n).model i) : ℝ) := by
  have hN : ∀ n, (0 : ℝ) ≤ Fintype.card (A.model n) := fun n ↦ Nat.cast_nonneg _
  have hMpos : 0 < Real.log (1 + 2 * η) - Real.log (1 - 2 * η) := by
    have hlt := Real.log_lt_log (by linarith : (0 : ℝ) < 1 - 2 * η)
      (by linarith : 1 - 2 * η < 1 + 2 * η)
    linarith
  have hcomp : ∀ q ∈ C.compressors, Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      (blockLabelVariation A DG E f (Real.log (1 + 2 * η) - Real.log (1 - 2 * η)) q) :=
    fun q hq ↦ blockCompressorLabel_negligible A DG hTsymm hTgen E f hMpos.le huncov q (π q)
      (Dom q) (Bad q) (κ q) (hκ q hq) (hκv q hq) (hone q hq) (hbad q hq) (hout q hq)
      (hmiss q hq)
  have hamb : ∀ g ∈ C.ambientGenerators, Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      (blockLabelVariation A DG E f (Real.log (1 + 2 * η) - Real.log (1 - 2 * η)) g) := by
    intro g hg
    classical
    simp only [CompressionSetup.ambientGenerators, Finset.mem_union, Finset.mem_image] at hg
    rcases hg with (hg | hg) | hg
    · obtain ⟨s, hs, rfl⟩ := hg
      exact blockInvariantLabel_negligible A DG hTsymm hTgen E f hMpos.le huncov
        (C.embedΓ s) (hΓ s hs)
    · exact hcomp g hg
    · obtain ⟨q, hq, rfl⟩ := hg
      exact clampedLabel_negligible_inv DG
        (logMedian DG (fun n ↦ blockObject (E n)) fun n ↦ optionObservable (f n))
        (fun n y ↦ logObservable (optionObservable (f n)) (blockObject (E n) y)) hMpos.le q
        (hcomp q hq)
  have hlabel : ∀ t' ∈ T, Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      (blockLabelVariation A DG E f (Real.log (1 + 2 * η) - Real.log (1 - 2 * η)) t') :=
    fun t' _ ↦ sum_abs_sub_negligible_of_closure A.model A.map A.hamming_mul_vanishing
      A.hamming_one_vanishing A.hamming_inv_vanishing
      (fun n ↦ clampedDeviation (DG.blocks n)
        (logMedian DG (fun n ↦ blockObject (E n)) (fun n ↦ optionObservable (f n)) n)
        (fun y ↦ logObservable (optionObservable (f n)) (blockObject (E n) y))
        (Real.log (1 + 2 * η) - Real.log (1 - 2 * η)))
      (fun n y ↦ abs_clampTo_le hMpos.le
        (logObservable (optionObservable (f n)) (blockObject (E n) y) -
          logMedian DG (fun n ↦ blockObject (E n)) (fun n ↦ optionObservable (f n)) n
            (blockIndexOf (DG.blocks n) y)))
      C.ambientGenerators_generate hamb t'
  have hleak : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ((matchLeak (blockObject (E n)) (A.map n t) (Option.map (π t n))
        ((Dom t n).image some)).card : ℝ) := by
    refine Negligible.mono_nonneg hN (fun n ↦ Nat.cast_nonneg _) (fun n ↦ ?_) (hmiss t ht)
    exact_mod_cast card_matchLeak_image_some_le (E n) (A.map n t) (π t n) (Dom t n)
  have hfail := failingWeight_negligible DG (fun n ↦ blockObject (E n))
    (fun n ↦ optionObservable (f n)) hMpos hlabel t (fun n ↦ Option.map (π t n))
    (fun n ↦ (Dom t n).image some) (DG.all_almost_invariant hTsymm hTgen t) hleak
  refine Negligible.mono_nonneg hN (fun n ↦ Finset.sum_nonneg fun i _ ↦ Nat.cast_nonneg _)
    (fun n ↦ ?_) hfail
  have hsub : ((Dom t n).filter (fun i ↦
      ¬ ((1 - 2 * η) ^ 2 * (f n (π t n i) : ℝ) ≤ (1 + 2 * η) ^ 2 * f n i ∧
        (1 - 2 * η) ^ 2 * (f n i : ℝ) ≤ (1 + 2 * η) ^ 2 * f n (π t n i)))).image some ⊆
      ((Dom t n).image some).filter fun o ↦
        2 * (Real.log (1 + 2 * η) - Real.log (1 - 2 * η)) <
          |logObservable (optionObservable (f n)) (Option.map (π t n) o) -
            logObservable (optionObservable (f n)) o| := by
    intro o ho
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ho
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_image_of_mem some hi.1, ?_⟩
    by_contra hle
    rw [not_lt] at hle
    have hc : |Real.log (max (f n (π t n i) : ℝ) 1) - Real.log (max (f n i : ℝ) 1)| ≤
        2 * (Real.log (1 + 2 * η) - Real.log (1 - 2 * η)) := hle
    have hc' : |Real.log (max (f n i : ℝ) 1) - Real.log (max (f n (π t n i) : ℝ) 1)| ≤
        2 * (Real.log (1 + 2 * η) - Real.log (1 - 2 * η)) := by
      rw [abs_sub_comm]
      exact hc
    exact hi.2 ⟨sq_mul_le_of_abs_logCut_sub_le (hf n (π t n i)) (hf n i) hη₂ hη hc,
      sq_mul_le_of_abs_logCut_sub_le (hf n i) (hf n (π t n i)) hη₂ hη hc'⟩
  have h₁ := sum_card_le_card_objectVertices_image_some (E n) ((Dom t n).filter (fun i ↦
      ¬ ((1 - 2 * η) ^ 2 * (f n (π t n i) : ℝ) ≤ (1 + 2 * η) ^ 2 * f n i ∧
        (1 - 2 * η) ^ 2 * (f n i : ℝ) ≤ (1 + 2 * η) ^ 2 * f n (π t n i))))
  have h₂ := Finset.card_le_card (objectVertices_mono (blockObject (E n)) hsub)
  exact_mod_cast h₁.trans h₂

end Asymptotic

end MedianVertexForm
end GroupApproximation
