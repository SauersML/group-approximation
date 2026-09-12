import GroupApproximation.KunThom.CentralizerNormalizationUniformGood

/-!
# The chosen good components and their completed collisions

`goodComponent` fixes the good predicate of `exists_goodComponents`, so that
later modules can refer to it.  `goodComponent_badMass`, `goodComponent_size`
and `goodComponent_errors` are its negligible bad mass, its diverging sizes
and its uniform raw error bounds.

Two completed labels of a component agree at a point only where the two
ambient labels agree or one of them leaves the component
(`card_completedCollision_le`).  Completed collisions of two distinct elements
are therefore uniformly a vanishing fraction of good components
(`eventually_completedCollision_le`).  This is the quantitative form needed to
keep labels injective after a small part of each component is removed.

`eventually_budget_mul_le` gives any fixed inequality `budget * b ≤ a |C|`
eventually on good components, and `negligible_badMass_and` adds an eventually
implied condition to a good predicate without changing the negligibility of
the bad mass.
-/

namespace GroupApproximation
namespace CentralizerNormalizationUniform

open scoped BigOperators

/-- The good components chosen by `exists_goodComponents`. -/
noncomputable def goodComponent {K : Type} [Group K] [Countable K] [Infinite K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (hsymm : ∀ t ∈ T, t⁻¹ ∈ T) (hgen : Subgroup.closure (T : Set K) = ⊤) :
    ∀ n, D.componentIndex n → Prop :=
  Classical.choose (exists_goodComponents D hsymm hgen)

open Classical in
theorem goodComponent_badMass {K : Type} [Group K] [Countable K] [Infinite K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (hsymm : ∀ t ∈ T, t⁻¹ ∈ T) (hgen : Subgroup.closure (T : Set K) = ⊤) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ∑ C : D.componentIndex n,
        if goodComponent D hsymm hgen n C then 0 else (C.block.card : ℝ)) :=
  (Classical.choose_spec (exists_goodComponents D hsymm hgen)).1

theorem goodComponent_size {K : Type} [Group K] [Countable K] [Infinite K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (hsymm : ∀ t ∈ T, t⁻¹ ∈ T) (hgen : Subgroup.closure (T : Set K) = ⊤) :
    ∀ M₀ : ℕ, ∃ M : ℕ, ∀ n ≥ M, ∀ C, goodComponent D hsymm hgen n C →
      M₀ ≤ C.block.card :=
  (Classical.choose_spec (exists_goodComponents D hsymm hgen)).2.2.1

theorem goodComponent_errors {K : Type} [Group K] [Countable K] [Infinite K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T)
    (hsymm : ∀ t ∈ T, t⁻¹ ∈ T) (hgen : Subgroup.closure (T : Set K) = ⊤) :
    ∀ (r : (K × K) ⊕ (K × K) ⊕ K ⊕ ℕ ⊕ Unit ⊕ Unit) (δ : ℝ), 0 < δ →
      ∃ M : ℕ, ∀ n ≥ M, ∀ C, goodComponent D hsymm hgen n C →
        componentError D r n C ≤ δ * C.block.card :=
  (Classical.choose_spec (exists_goodComponents D hsymm hgen)).2.2.2.2.2.2

/-- A finite set covered by three finite sets has at most their total size. -/
theorem card_le_card_add_card_add_card_of_subset {α : Type*} [DecidableEq α]
    {s A B E : Finset α} (h : ∀ x ∈ s, x ∈ A ∨ x ∈ B ∨ x ∈ E) :
    s.card ≤ A.card + B.card + E.card := by
  have hsub : s ⊆ (A ∪ B) ∪ E := by
    intro x hx
    rcases h x hx with hx | hx | hx
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
    · exact Finset.mem_union_right _ hx
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (A ∪ B) E
  have h3 := Finset.card_union_le A B
  omega

/-- Completed labels agree only at ambient collisions or exits. -/
theorem card_completedCollision_le {K : Type} [Group K] {S : SoficApproximation K}
    {T : Finset K} (D : ExpanderDecomposition S T) (n : ℕ) (C : D.componentIndex n)
    (g h : K) :
    (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
        D.componentCompletedAction n C g x = D.componentCompletedAction n C h x).card ≤
      componentCollisionCount D n C g h +
        (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n g (x : S.model n) ∉ C.block).card +
        (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n h (x : S.model n) ∉ C.block).card := by
  unfold componentCollisionCount
  apply card_le_card_add_card_add_card_of_subset
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  by_cases hg : S.map n g (x : S.model n) ∈ C.block
  · by_cases hh : S.map n h (x : S.model n) ∈ C.block
    · left
      rw [← D.componentCompletedAction_agrees n C g x hg,
        ← D.componentCompletedAction_agrees n C h x hh, hx]
    · exact Or.inr (Or.inr hh)
  · exact Or.inr (Or.inl hg)

open Classical in
/-- Completed collisions of two distinct elements are uniformly small on
components whose raw errors are uniformly small. -/
theorem eventually_completedCollision_le {K : Type} [Group K] {S : SoficApproximation K}
    {T : Finset K} (D : ExpanderDecomposition S T) (good : ∀ n, D.componentIndex n → Prop)
    (herr : ∀ (r : (K × K) ⊕ (K × K) ⊕ K ⊕ ℕ ⊕ Unit ⊕ Unit) (δ : ℝ), 0 < δ →
      ∃ M : ℕ, ∀ n ≥ M, ∀ C, good n C → componentError D r n C ≤ δ * C.block.card)
    {g h : K} (hgh : g ≠ h) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℕ, ∀ n ≥ M, ∀ C, good n C →
      ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
        D.componentCompletedAction n C g x = D.componentCompletedAction n C h x).card : ℝ) ≤
        δ * C.block.card := by
  have hδ3 : 0 < δ / 3 := div_pos hδ (by norm_num)
  obtain ⟨M1, hM1⟩ := herr (Sum.inr (Sum.inl (g, h))) (δ / 3) hδ3
  obtain ⟨M2, hM2⟩ := herr (Sum.inr (Sum.inr (Sum.inl g))) (δ / 3) hδ3
  obtain ⟨M3, hM3⟩ := herr (Sum.inr (Sum.inr (Sum.inl h))) (δ / 3) hδ3
  refine ⟨max M1 (max M2 M3), fun n hn C hC ↦ ?_⟩
  have hn1 : M1 ≤ n := (le_max_left _ _).trans hn
  have hn2 : M2 ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn3 : M3 ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  have h1 : (if g = h then (0 : ℝ) else (componentCollisionCount D n C g h : ℝ)) ≤
      δ / 3 * (C.block.card : ℝ) :=
    (componentError_collision D (g, h) n C).symm.trans_le (hM1 n hn1 C hC)
  rw [if_neg hgh] at h1
  have h2 : ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
      S.map n g (x : S.model n) ∉ C.block).card : ℝ) ≤ δ / 3 * (C.block.card : ℝ) :=
    (componentError_exit D g n C).symm.trans_le (hM2 n hn2 C hC)
  have h3 : ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
      S.map n h (x : S.model n) ∉ C.block).card : ℝ) ≤ δ / 3 * (C.block.card : ℝ) :=
    (componentError_exit D h n C).symm.trans_le (hM3 n hn3 C hC)
  have hcount : ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
        D.componentCompletedAction n C g x = D.componentCompletedAction n C h x).card : ℝ) ≤
      (componentCollisionCount D n C g h : ℝ) +
        ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n g (x : S.model n) ∉ C.block).card : ℝ) +
        ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n h (x : S.model n) ∉ C.block).card : ℝ) := by
    exact_mod_cast card_completedCollision_le D n C g h
  linarith

/-- Any fixed inequality `budget * b ≤ a |C|` with `a > 0` holds eventually on
components whose raw errors are uniformly small. -/
theorem eventually_budget_mul_le {K : Type} [Group K] {S : SoficApproximation K}
    {T : Finset K} (D : ExpanderDecomposition S T) (good : ∀ n, D.componentIndex n → Prop)
    (herr : ∀ (r : (K × K) ⊕ (K × K) ⊕ K ⊕ ℕ ⊕ Unit ⊕ Unit) (δ : ℝ), 0 < δ →
      ∃ M : ℕ, ∀ n ≥ M, ∀ C, good n C → componentError D r n C ≤ δ * C.block.card)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ M : ℕ, ∀ n ≥ M, ∀ C, good n C →
      (D.componentLabelEditBudget n C : ℝ) * b ≤ a * C.block.card := by
  have hb1 : 0 < b + 1 := by linarith
  obtain ⟨M, hM⟩ := herr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))))
    (a / (b + 1)) (div_pos ha hb1)
  refine ⟨M, fun n hn C hC ↦ ?_⟩
  have h1 : (D.componentLabelEditBudget n C : ℝ) ≤ a / (b + 1) * C.block.card :=
    (componentError_budget D () n C).symm.trans_le (hM n hn C hC)
  have hB0 : (0 : ℝ) ≤ D.componentLabelEditBudget n C := Nat.cast_nonneg _
  have h2 : (D.componentLabelEditBudget n C : ℝ) * (b + 1) ≤ a * C.block.card := by
    calc (D.componentLabelEditBudget n C : ℝ) * (b + 1)
        ≤ a / (b + 1) * C.block.card * (b + 1) := mul_le_mul_of_nonneg_right h1 hb1.le
      _ = a * C.block.card := by
        rw [mul_right_comm, div_mul_cancel₀ a hb1.ne']
  linarith

open Classical in
/-- An eventually implied condition leaves the bad weight negligible. -/
theorem negligible_badMass_and {ι : ℕ → Type*} [∀ n, Fintype (ι n)] {N : ℕ → ℝ}
    (hN : ∀ n, 0 ≤ N n) (w : ∀ n, ι n → ℝ) (hw : ∀ n i, 0 ≤ w n i)
    (P Q : ∀ n, ι n → Prop)
    (hP : Negligible N fun n ↦ ∑ i, if P n i then 0 else w n i)
    (hQ : ∃ M : ℕ, ∀ n ≥ M, ∀ i, P n i → Q n i) :
    Negligible N fun n ↦ ∑ i, if P n i ∧ Q n i then 0 else w n i := by
  obtain ⟨M, hM⟩ := hQ
  refine Vanishing.squeeze_eventually hP M fun n hn ↦ ⟨?_, ?_⟩
  · apply div_nonneg _ (hN n)
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact le_rfl
    · exact hw n i
  · apply div_le_div_of_nonneg_right _ (hN n)
    apply Finset.sum_le_sum
    intro i _
    by_cases hPi : P n i
    · rw [if_pos (show P n i ∧ Q n i from ⟨hPi, hM n hn i hPi⟩), if_pos hPi]
    · rw [if_neg (show ¬ (P n i ∧ Q n i) from fun hPQ ↦ hPi hPQ.1), if_neg hPi]

end CentralizerNormalizationUniform
end GroupApproximation
