import GroupApproximation.KunThom.CentralizerNormalizationUniformMarkov
import GroupApproximation.Matching.ComponentClusterScale
import GroupApproximation.Matching.ComponentCompletedMultiplicativity
import Mathlib.Data.Countable.Basic

/-!
# Good components of an expander decomposition

For an expander decomposition `D` of a sofic approximation of an infinite
countable group, `exists_goodComponents` selects a predicate of good
components carrying all but a negligible part of the model mass, on which the
completed component actions of `ComponentLabelCompletion` are uniformly
controlled for large indices:

* for every fixed pair `g, h`, the normalized multiplication error of the
  completed labels tends to zero uniformly over good components;
* the sizes of good components tend to infinity uniformly;
* the completed labels of the elements of `T` are eventually injective;
* good components are eventually cluster good (`IsClusterGood`);
* the local edit budget is uniformly a vanishing fraction of the size.

The proof applies the diagonal Markov selection of
`CentralizerNormalizationUniformMarkov` to six countable families of
per-component error counts: completed multiplication errors, ambient
collisions of two elements, ambient exits from the component, small
components, components that are not cluster good, and local edit budgets.
Each family has negligible total by the landed component estimates.
-/

namespace GroupApproximation
namespace CentralizerNormalizationUniform

open scoped BigOperators

theorem card_indexedBlockModel {Y : FiniteModel} (Q : BlockStructure Y)
    (B : BlockIndex Q) : Fintype.card (indexedBlockModel Q B) = B.block.card := by
  simp [indexedBlockModel]

/-- A finite type covered by three finite sets has at most their total size. -/
theorem card_le_card_add_card_add_card {α : Type*} [Fintype α] [DecidableEq α]
    (A B E : Finset α) (h : ∀ x, x ∈ A ∨ x ∈ B ∨ x ∈ E) :
    Fintype.card α ≤ A.card + B.card + E.card := by
  have hsub : (Finset.univ : Finset α) ⊆ (A ∪ B) ∪ E := by
    intro x _
    rcases h x with hx | hx | hx
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
    · exact Finset.mem_union_right _ hx
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (A ∪ B) E
  have h3 := Finset.card_union_le A B
  rw [Finset.card_univ] at h1
  omega

/-- Points of a component at which two ambient permutations agree. -/
noncomputable def componentCollisionCount {K : Type} [Group K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (n : ℕ) (C : D.componentIndex n) (g h : K) : ℕ :=
  (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
    S.map n g (x : S.model n) = S.map n h (x : S.model n)).card

theorem sum_componentCollisionCount {K : Type} [Group K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (n : ℕ) (g h : K) :
    (∑ C : D.componentIndex n, (componentCollisionCount D n C g h : ℝ)) =
      ((S.collisionError n g h).card : ℝ) := by
  simpa only [componentCollisionCount, SoficApproximation.collisionError] using
    BlockIndex.sum_card_filter (D.blocks n)
      (fun x : S.model n ↦ S.map n g x = S.map n h x)

/-- Exits of a fixed element from the components have negligible total. -/
theorem componentExit_sum_negligible {K : Type} [Group K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (hsymm : ∀ t ∈ T, t⁻¹ ∈ T) (hgen : Subgroup.closure (T : Set K) = ⊤) (g : K) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ∑ C : D.componentIndex n,
        ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n g (x : S.model n) ∉ C.block).card : ℝ)) := by
  have hall := D.all_almost_invariant hsymm hgen g
  change Negligible S.cardScale.value
    (fun n ↦ ((wordCrossing (D.blocks n) (S.map n g)).card : ℝ)) at hall
  refine Negligible.congr ?_ fun n ↦ (D.sum_componentGeneratorExits n g).symm
  change Negligible S.cardScale.value (fun n ↦
    ((Finset.univ.filter fun y : S.model n ↦
      (D.blocks n).block (S.map n g y) ≠ (D.blocks n).block y).card : ℝ))
  simpa only [wordCrossing] using hall

open Classical in
/-- Six countable families of per-component error counts. -/
noncomputable def componentError {K : Type} [Group K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T) :
    (K × K) ⊕ (K × K) ⊕ K ⊕ ℕ ⊕ Unit ⊕ Unit → ∀ n, D.componentIndex n → ℝ :=
  Sum.elim (fun p n C ↦ ((D.componentMultiplicationError n C p.1 p.2).card : ℝ))
    (Sum.elim
      (fun p n C ↦ if p.1 = p.2 then 0 else (componentCollisionCount D n C p.1 p.2 : ℝ))
      (Sum.elim
        (fun g n C ↦ ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n g (x : S.model n) ∉ C.block).card : ℝ))
        (Sum.elim
          (fun M _ C ↦ if (C.block.card : ℝ) ≤ M then (C.block.card : ℝ) else 0)
          (Sum.elim
            (fun _ n C ↦ if D.IsClusterGood n C then 0 else (C.block.card : ℝ))
            (fun _ n C ↦ (D.componentLabelEditBudget n C : ℝ))))))

theorem componentError_mul {K : Type} [Group K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (p : K × K) (n : ℕ) (C : D.componentIndex n) :
    componentError D (Sum.inl p) n C =
      ((D.componentMultiplicationError n C p.1 p.2).card : ℝ) := rfl

open Classical in
theorem componentError_collision {K : Type} [Group K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (p : K × K) (n : ℕ) (C : D.componentIndex n) :
    componentError D (Sum.inr (Sum.inl p)) n C =
      if p.1 = p.2 then 0 else (componentCollisionCount D n C p.1 p.2 : ℝ) := rfl

theorem componentError_exit {K : Type} [Group K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (g : K) (n : ℕ) (C : D.componentIndex n) :
    componentError D (Sum.inr (Sum.inr (Sum.inl g))) n C =
      ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
        S.map n g (x : S.model n) ∉ C.block).card : ℝ) := rfl

theorem componentError_small {K : Type} [Group K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (M n : ℕ) (C : D.componentIndex n) :
    componentError D (Sum.inr (Sum.inr (Sum.inr (Sum.inl M)))) n C =
      if (C.block.card : ℝ) ≤ M then (C.block.card : ℝ) else 0 := rfl

open Classical in
theorem componentError_cluster {K : Type} [Group K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (u : Unit) (n : ℕ) (C : D.componentIndex n) :
    componentError D (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl u))))) n C =
      if D.IsClusterGood n C then 0 else (C.block.card : ℝ) := rfl

theorem componentError_budget {K : Type} [Group K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (u : Unit) (n : ℕ) (C : D.componentIndex n) :
    componentError D (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr u))))) n C =
      (D.componentLabelEditBudget n C : ℝ) := rfl

theorem componentError_nonneg {K : Type} [Group K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (r : (K × K) ⊕ (K × K) ⊕ K ⊕ ℕ ⊕ Unit ⊕ Unit) (n : ℕ)
    (C : D.componentIndex n) : 0 ≤ componentError D r n C := by
  rcases r with p | p | g | M | u | u
  · rw [componentError_mul]
    positivity
  · rw [componentError_collision]
    split_ifs
    · exact le_rfl
    · positivity
  · rw [componentError_exit]
    positivity
  · rw [componentError_small]
    split_ifs
    · positivity
    · exact le_rfl
  · rw [componentError_cluster]
    split_ifs
    · exact le_rfl
    · positivity
  · rw [componentError_budget]
    positivity

/-- Every error family has negligible total at the model scale. -/
theorem componentError_sum_negligible {K : Type} [Group K] [Infinite K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (hsymm : ∀ t ∈ T, t⁻¹ ∈ T) (hgen : Subgroup.closure (T : Set K) = ⊤)
    (r : (K × K) ⊕ (K × K) ⊕ K ⊕ ℕ ⊕ Unit ⊕ Unit) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ∑ C : D.componentIndex n, componentError D r n C) := by
  rcases r with p | p | g | M | u | u
  · exact Negligible.congr
      (D.componentMultiplicationError_sum_negligible hsymm hgen p.1 p.2)
      fun n ↦ Finset.sum_congr rfl fun C _ ↦ (componentError_mul D p n C).symm
  · by_cases hp : p.1 = p.2
    · refine Negligible.congr Negligible.zero fun n ↦ ?_
      symm
      apply Finset.sum_eq_zero
      intro C _
      rw [componentError_collision, if_pos hp]
    · refine Negligible.congr (S.collisionError_negligible p.1 p.2 hp) fun n ↦ ?_
      rw [← sum_componentCollisionCount D n p.1 p.2]
      apply Finset.sum_congr rfl
      intro C _
      rw [componentError_collision, if_neg hp]
  · exact Negligible.congr (componentExit_sum_negligible D hsymm hgen g)
      fun n ↦ Finset.sum_congr rfl fun C _ ↦ (componentError_exit D g n C).symm
  · exact Negligible.congr (D.smallBlockVertices_negligible hsymm hgen M)
      fun n ↦ (sum_smallBlock_card (D.blocks n) M).symm.trans
        (Finset.sum_congr rfl fun C _ ↦ (componentError_small D M n C).symm)
  · refine Negligible.congr (D.badClusterComponentMass_negligible hsymm hgen)
      fun n ↦ ?_
    unfold ExpanderDecomposition.badClusterComponentMass
    apply Finset.sum_congr rfl
    intro C _
    by_cases hC : D.IsClusterGood n C <;>
      simp only [hC, ↓reduceIte, componentError_cluster]
  · exact Negligible.congr D.componentLabelEditBudget_sum_negligible
      fun n ↦ Finset.sum_congr rfl fun C _ ↦ (componentError_budget D u n C).symm

/-- Normalized multiplication error of the completed labels on a component. -/
theorem hammingDistance_componentCompletedAction {K : Type} [Group K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (n : ℕ) (C : D.componentIndex n) (g h : K) :
    hammingDistance (indexedBlockModel (D.blocks n) C)
        (D.componentCompletedAction n C (g * h))
        (D.componentCompletedAction n C g * D.componentCompletedAction n C h) =
      ((D.componentMultiplicationError n C g h).card : ℝ) / (C.block.card : ℝ) := by
  have hset : hammingDisagreement (D.componentCompletedAction n C (g * h))
      (D.componentCompletedAction n C g * D.componentCompletedAction n C h) =
      D.componentMultiplicationError n C g h := by
    ext x
    simp only [mem_hammingDisagreement, ExpanderDecomposition.componentMultiplicationError,
      Finset.mem_filter, Finset.mem_univ, true_and]
  unfold hammingDistance
  rw [hset, card_indexedBlockModel]

/-- A local edit budget of at most `ρ · cheeger / 4` times the component size
gives tagged expansion of the completed labels at the scale `⌈ρ |C|⌉₊`. -/
theorem taggedExpansion_ceil_of_budget_le {K : Type} [Group K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (n : ℕ) (C : D.componentIndex n) {ρ : ℝ} (hρ : 0 < ρ)
    (hbudget : (D.componentLabelEditBudget n C : ℝ) ≤
      ρ * D.cheeger / 4 * C.block.card) :
    FinitePartialBijection.HasTaggedExpansionAtScale
      (fun t : T ↦ D.componentCompletedAction n C t.1) (D.cheeger / 4)
      ⌈ρ * (C.block.card : ℝ)⌉₊ := by
  apply D.componentCompletedAction_taggedExpansion
  have hc := D.cheeger_pos
  have hp : (0 : ℝ) < C.block.card := by
    exact_mod_cast Finset.card_pos.mpr (BlockIndex.block_nonempty (D.blocks n) C)
  have hceil : ρ * (C.block.card : ℝ) ≤ ((⌈ρ * (C.block.card : ℝ)⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil _
  have h1 : D.cheeger * (ρ * (C.block.card : ℝ)) ≤
      D.cheeger * ((⌈ρ * (C.block.card : ℝ)⌉₊ : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hceil hc.le
  have h2 : 0 < D.cheeger * (ρ * (C.block.card : ℝ)) := mul_pos hc (mul_pos hρ hp)
  linarith

open Classical in
/-- **Good components** of an expander decomposition (blueprint step G1f). -/
theorem exists_goodComponents {K : Type} [Group K] [Countable K] [Infinite K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (hsymm : ∀ t ∈ T, t⁻¹ ∈ T) (hgen : Subgroup.closure (T : Set K) = ⊤) :
    ∃ good : ∀ n, D.componentIndex n → Prop,
      Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
          (fun n ↦ ∑ C : D.componentIndex n,
            if good n C then 0 else (C.block.card : ℝ)) ∧
        (∀ (g h : K) (δ : ℝ), 0 < δ → ∃ M : ℕ, ∀ n ≥ M, ∀ C, good n C →
          hammingDistance (indexedBlockModel (D.blocks n) C)
            (D.componentCompletedAction n C (g * h))
            (D.componentCompletedAction n C g * D.componentCompletedAction n C h) < δ) ∧
        (∀ M₀ : ℕ, ∃ M : ℕ, ∀ n ≥ M, ∀ C, good n C → M₀ ≤ C.block.card) ∧
        (∃ M : ℕ, ∀ n ≥ M, ∀ C, good n C →
          Set.InjOn (D.componentCompletedAction n C) (T : Set K)) ∧
        (∃ M : ℕ, ∀ n ≥ M, ∀ C, good n C → D.IsClusterGood n C) ∧
        (∀ δ : ℝ, 0 < δ → ∃ M : ℕ, ∀ n ≥ M, ∀ C, good n C →
          (D.componentLabelEditBudget n C : ℝ) ≤ δ * C.block.card) ∧
        (∀ (r : (K × K) ⊕ (K × K) ⊕ K ⊕ ℕ ⊕ Unit ⊕ Unit) (δ : ℝ), 0 < δ →
          ∃ M : ℕ, ∀ n ≥ M, ∀ C, good n C →
            componentError D r n C ≤ δ * C.block.card) := by
  haveI : Nonempty ((K × K) ⊕ (K × K) ⊕ K ⊕ ℕ ⊕ Unit ⊕ Unit) :=
    ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inl 0)))⟩
  obtain ⟨good, hbad, herr⟩ := exists_isGood (ι := fun n ↦ D.componentIndex n)
    (fun n ↦ (Fintype.card (S.model n) : ℝ)) (fun _ ↦ Nat.cast_nonneg _)
    (fun n (C : D.componentIndex n) ↦ (C.block.card : ℝ)) (fun _ _ ↦ Nat.cast_nonneg _)
    (componentError D) (componentError_nonneg D)
    (componentError_sum_negligible D hsymm hgen)
  have hpos : ∀ n (C : D.componentIndex n), (0 : ℝ) < C.block.card := fun n C ↦ by
    exact_mod_cast Finset.card_pos.mpr (BlockIndex.block_nonempty (D.blocks n) C)
  refine ⟨good, hbad, ?_, ?_, ?_, ?_, ?_, herr⟩
  · intro g h δ hδ
    obtain ⟨M, hM⟩ := herr (Sum.inl (g, h)) (δ / 2) (half_pos hδ)
    refine ⟨M, fun n hn C hC ↦ ?_⟩
    have hle : ((D.componentMultiplicationError n C g h).card : ℝ) ≤
        δ / 2 * (C.block.card : ℝ) :=
      (componentError_mul D (g, h) n C).symm.trans_le (hM n hn C hC)
    rw [hammingDistance_componentCompletedAction D n C g h, div_lt_iff₀ (hpos n C)]
    linarith [mul_pos hδ (hpos n C)]
  · intro M₀
    obtain ⟨M, hM⟩ := herr (Sum.inr (Sum.inr (Sum.inr (Sum.inl M₀)))) (1 / 2)
      (by norm_num)
    refine ⟨M, fun n hn C hC ↦ ?_⟩
    have hle : (if (C.block.card : ℝ) ≤ M₀ then (C.block.card : ℝ) else 0) ≤
        1 / 2 * (C.block.card : ℝ) :=
      (componentError_small D M₀ n C).symm.trans_le (hM n hn C hC)
    by_contra hsmall
    have hsmall' : (C.block.card : ℝ) ≤ M₀ := by
      have h' : C.block.card ≤ M₀ := by omega
      exact_mod_cast h'
    rw [if_pos hsmall'] at hle
    linarith [hpos n C]
  · have hcoll : ∀ p : K × K, ∃ M : ℕ, ∀ n ≥ M, ∀ C, good n C →
        componentError D (Sum.inr (Sum.inl p)) n C ≤ 1 / 4 * (C.block.card : ℝ) :=
      fun p ↦ herr (Sum.inr (Sum.inl p)) (1 / 4) (by norm_num)
    have hexit : ∀ g : K, ∃ M : ℕ, ∀ n ≥ M, ∀ C, good n C →
        componentError D (Sum.inr (Sum.inr (Sum.inl g))) n C ≤
          1 / 4 * (C.block.card : ℝ) :=
      fun g ↦ herr (Sum.inr (Sum.inr (Sum.inl g))) (1 / 4) (by norm_num)
    choose Mc hMc using hcoll
    choose Me hMe using hexit
    refine ⟨(T ×ˢ T).sup fun p ↦ max (Mc p) (max (Me p.1) (Me p.2)),
      fun n hn C hC t ht t' ht' hTeq ↦ ?_⟩
    by_contra hne
    have hMp : max (Mc (t, t')) (max (Me t) (Me t')) ≤
        (T ×ˢ T).sup fun p ↦ max (Mc p) (max (Me p.1) (Me p.2)) :=
      Finset.le_sup (f := fun p ↦ max (Mc p) (max (Me p.1) (Me p.2)))
        (Finset.mem_product.mpr ⟨Finset.mem_coe.mp ht, Finset.mem_coe.mp ht'⟩)
    have hn1 : Mc (t, t') ≤ n := ((le_max_left _ _).trans hMp).trans hn
    have hn2 : Me t ≤ n :=
      (((le_max_left _ _).trans (le_max_right _ _)).trans hMp).trans hn
    have hn3 : Me t' ≤ n :=
      (((le_max_right _ _).trans (le_max_right _ _)).trans hMp).trans hn
    have h1' : (if t = t' then (0 : ℝ) else (componentCollisionCount D n C t t' : ℝ)) ≤
        1 / 4 * (C.block.card : ℝ) :=
      (componentError_collision D (t, t') n C).symm.trans_le (hMc (t, t') n hn1 C hC)
    rw [if_neg hne] at h1'
    have h2 : ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
        S.map n t (x : S.model n) ∉ C.block).card : ℝ) ≤ 1 / 4 * (C.block.card : ℝ) :=
      (componentError_exit D t n C).symm.trans_le (hMe t n hn2 C hC)
    have h3 : ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
        S.map n t' (x : S.model n) ∉ C.block).card : ℝ) ≤ 1 / 4 * (C.block.card : ℝ) :=
      (componentError_exit D t' n C).symm.trans_le (hMe t' n hn3 C hC)
    have hcover : ∀ x : indexedBlockModel (D.blocks n) C,
        x ∈ (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n t (x : S.model n) = S.map n t' (x : S.model n)) ∨
        x ∈ (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n t (x : S.model n) ∉ C.block) ∨
        x ∈ (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n t' (x : S.model n) ∉ C.block) := by
      intro x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hx1 : S.map n t (x : S.model n) ∈ C.block
      · by_cases hx2 : S.map n t' (x : S.model n) ∈ C.block
        · left
          rw [← D.componentCompletedAction_agrees n C t x hx1,
            ← D.componentCompletedAction_agrees n C t' x hx2, hTeq]
        · exact Or.inr (Or.inr hx2)
      · exact Or.inr (Or.inl hx1)
    have hcount : (C.block.card : ℝ) ≤ (componentCollisionCount D n C t t' : ℝ) +
        ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n t (x : S.model n) ∉ C.block).card : ℝ) +
        ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n t' (x : S.model n) ∉ C.block).card : ℝ) := by
      have h := card_le_card_add_card_add_card _ _ _ hcover
      rw [card_indexedBlockModel] at h
      exact_mod_cast h
    linarith [hpos n C]
  · obtain ⟨M, hM⟩ := herr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))))
      (1 / 2) (by norm_num)
    refine ⟨M, fun n hn C hC ↦ ?_⟩
    have hle : (if D.IsClusterGood n C then (0 : ℝ) else (C.block.card : ℝ)) ≤
        1 / 2 * (C.block.card : ℝ) :=
      (componentError_cluster D () n C).symm.trans_le (hM n hn C hC)
    by_contra hbadC
    rw [if_neg hbadC] at hle
    linarith [hpos n C]
  · intro δ hδ
    obtain ⟨M, hM⟩ := herr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))) δ hδ
    exact ⟨M, fun n hn C hC ↦
      (componentError_budget D () n C).symm.trans_le (hM n hn C hC)⟩

end CentralizerNormalizationUniform
end GroupApproximation
