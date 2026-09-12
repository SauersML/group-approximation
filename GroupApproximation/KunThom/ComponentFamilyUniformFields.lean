import GroupApproximation.Sofic.Sofic
import GroupApproximation.Matching.ComponentLabelCompletion

/-!
# Uniform fields of a component family on retained sets

`CentralizerNormalizationImprove.ComponentFamily` asks for sizes tending to
infinity, local multiplicativity and injective labels, uniformly over the
objects at each index.  Its producer restricts every good expander component to
a retained set `V`, obtained by removing a sparse cut, and completes the labels
there.  This module transfers the three uniform fields from the full models to
the retained ones.  It does not depend on how `V` is chosen: any removed set
of vanishing proportion works, and so does any completion that agrees with the
ambient label wherever the image stays in `V`.

*Finite estimates on one model.*

* `card_hammingDisagreement_subset_mul_le`: a product failure of the retained
  labels is an ambient product failure, or one of three images leaves `V`.
* `card_le_collision_add_of_subset_eq`: two equal retained labels force
  ambient collisions on all but twice the removed count of the points of `V`.

*Uniform fields over a family `ι n` of objects.*

* `size_tendsTo_subset`: sizes tend to infinity once at most half of each
  model is removed.
* `locallyMultiplicative_subset`: normalized multiplication errors vanish
  uniformly once the removed proportion vanishes uniformly.
* `labelsInjective_subset`: the retained labels of a finite set `T` are
  eventually injective, once ambient collisions of distinct elements of `T`
  cover at most a quarter of each model and at most an eighth is removed.

*Completed component labels.*  `card_componentCompletedAction_collision_le`
bounds the collisions of two completed labels on an expander component by the
ambient collisions and the exits of both elements from the component.
-/

namespace GroupApproximation
namespace ComponentFamilyUniformFields

/-- A finite subset of a finite model, as a finite model. -/
abbrev subsetModel (Y : FiniteModel) (V : Finset Y) : FiniteModel where
  carrier := V
  fintype := inferInstance
  decidableEq := inferInstance

theorem card_subsetModel (Y : FiniteModel) (V : Finset Y) :
    Fintype.card (subsetModel Y V) = V.card :=
  Fintype.card_coe V

theorem card_sdiff_add_card (Y : FiniteModel) (V : Finset Y) :
    (Finset.univ \ V).card + V.card = Fintype.card Y := by
  rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ V), Finset.card_univ]

/-- A permutation sends at most `|B|` points into `B`. -/
theorem card_filter_apply_mem_le {Y : FiniteModel} (σ : Equiv.Perm Y) (B : Finset Y) :
    (Finset.univ.filter fun y : Y ↦ σ y ∈ B).card ≤ B.card := by
  have himage : (Finset.univ.filter fun y : Y ↦ σ y ∈ B).image σ ⊆ B := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp hy).2
  calc (Finset.univ.filter fun y : Y ↦ σ y ∈ B).card
      = ((Finset.univ.filter fun y : Y ↦ σ y ∈ B).image σ).card :=
        (Finset.card_image_of_injective _ σ.injective).symm
    _ ≤ B.card := Finset.card_le_card himage

/-- Four-fold union bound. -/
theorem card_union_four_le {α : Type*} [DecidableEq α] (P Q₁ Q₂ Q₃ : Finset α) :
    (P ∪ Q₁ ∪ Q₂ ∪ Q₃).card ≤ P.card + Q₁.card + Q₂.card + Q₃.card := by
  have h₁ := Finset.card_union_le (P ∪ Q₁ ∪ Q₂) Q₃
  have h₂ := Finset.card_union_le (P ∪ Q₁) Q₂
  have h₃ := Finset.card_union_le P Q₁
  omega

/-- **Retained product failures.**  A point of `V` where the retained labels
fail the product law is an ambient product failure, or one of the three images
`h x`, `(g h) x`, `(g * h) x` leaves `V`. -/
theorem card_hammingDisagreement_subset_mul_le {K : Type*} [Mul K] {Y : FiniteModel}
    (V : Finset Y) (act : K → Equiv.Perm Y) (ract : K → Equiv.Perm (subsetModel Y V))
    (hagree : ∀ (g : K) (x : subsetModel Y V),
      act g (x : Y) ∈ V → (ract g x : Y) = act g x)
    (g h : K) :
    (hammingDisagreement (ract (g * h)) (ract g * ract h)).card ≤
      (hammingDisagreement (act (g * h)) (act g * act h)).card +
        3 * (Finset.univ \ V).card := by
  have hsub : (hammingDisagreement (ract (g * h)) (ract g * ract h)).image Subtype.val ⊆
      hammingDisagreement (act (g * h)) (act g * act h) ∪
        (Finset.univ.filter fun y : Y ↦ act h y ∈ Finset.univ \ V) ∪
        (Finset.univ.filter fun y : Y ↦ (act g * act h) y ∈ Finset.univ \ V) ∪
        (Finset.univ.filter fun y : Y ↦ act (g * h) y ∈ Finset.univ \ V) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [mem_hammingDisagreement] at hx
    by_cases h₁ : act h (x : Y) ∈ V
    · by_cases h₂ : (act g * act h) (x : Y) ∈ V
      · by_cases h₃ : act (g * h) (x : Y) ∈ V
        · apply Finset.mem_union_left
          apply Finset.mem_union_left
          apply Finset.mem_union_left
          rw [mem_hammingDisagreement]
          intro hamb
          apply hx
          apply Subtype.ext
          have e₁ : (ract h x : Y) = act h x := hagree h x h₁
          have h₂' : act g ((ract h x : subsetModel Y V) : Y) ∈ V := by
            rw [e₁]
            exact h₂
          have e₂ : (ract g (ract h x) : Y) = act g (act h x) := by
            rw [hagree g (ract h x) h₂', e₁]
          have e₃ : (ract (g * h) x : Y) = act (g * h) x := hagree (g * h) x h₃
          rw [Equiv.Perm.mul_apply, e₂, e₃]
          exact hamb
        · apply Finset.mem_union_right
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
          exact h₃
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
        exact h₂
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
      exact h₁
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hcard
  have hunion := card_union_four_le (hammingDisagreement (act (g * h)) (act g * act h))
    (Finset.univ.filter fun y : Y ↦ act h y ∈ Finset.univ \ V)
    (Finset.univ.filter fun y : Y ↦ (act g * act h) y ∈ Finset.univ \ V)
    (Finset.univ.filter fun y : Y ↦ act (g * h) y ∈ Finset.univ \ V)
  have hq₁ := card_filter_apply_mem_le (act h) (Finset.univ \ V)
  have hq₂ := card_filter_apply_mem_le (act g * act h) (Finset.univ \ V)
  have hq₃ := card_filter_apply_mem_le (act (g * h)) (Finset.univ \ V)
  omega

/-- **Retained collisions.**  If two retained labels agree, the two ambient
labels collide on all points of `V` except those with an image outside `V`. -/
theorem card_le_collision_add_of_subset_eq {Y : FiniteModel} (V : Finset Y)
    (σ τ : Equiv.Perm Y) (σ' τ' : Equiv.Perm (subsetModel Y V))
    (hσ : ∀ x : subsetModel Y V, σ (x : Y) ∈ V → (σ' x : Y) = σ x)
    (hτ : ∀ x : subsetModel Y V, τ (x : Y) ∈ V → (τ' x : Y) = τ x)
    (heq : σ' = τ') :
    V.card ≤ (Finset.univ.filter fun y : Y ↦ σ y = τ y).card +
      2 * (Finset.univ \ V).card := by
  have hsub : V ⊆ (Finset.univ.filter fun y : Y ↦ σ y = τ y) ∪
      (Finset.univ.filter fun y : Y ↦ σ y ∈ Finset.univ \ V) ∪
      (Finset.univ.filter fun y : Y ↦ τ y ∈ Finset.univ \ V) := by
    intro y hy
    by_cases h₁ : σ y ∈ V
    · by_cases h₂ : τ y ∈ V
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have e₁ : (σ' ⟨y, hy⟩ : Y) = σ y := hσ ⟨y, hy⟩ h₁
        have e₂ : (τ' ⟨y, hy⟩ : Y) = τ y := hτ ⟨y, hy⟩ h₂
        rw [← e₁, ← e₂, heq]
      · apply Finset.mem_union_right
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
        exact h₂
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
      exact h₁
  have hcard := Finset.card_le_card hsub
  have hu₁ := Finset.card_union_le ((Finset.univ.filter fun y : Y ↦ σ y = τ y) ∪
      (Finset.univ.filter fun y : Y ↦ σ y ∈ Finset.univ \ V))
    (Finset.univ.filter fun y : Y ↦ τ y ∈ Finset.univ \ V)
  have hu₂ := Finset.card_union_le (Finset.univ.filter fun y : Y ↦ σ y = τ y)
    (Finset.univ.filter fun y : Y ↦ σ y ∈ Finset.univ \ V)
  have hq₁ := card_filter_apply_mem_le σ (Finset.univ \ V)
  have hq₂ := card_filter_apply_mem_le τ (Finset.univ \ V)
  omega

/-! ## Uniform fields over a family of objects -/

/-- **Sizes.**  If the models have sizes tending to infinity uniformly and at
most half of each model is eventually removed, then the retained sets have
sizes tending to infinity uniformly. -/
theorem size_tendsTo_subset {ι : ℕ → Type} {Y : ∀ n, ι n → FiniteModel}
    (V : ∀ n (i : ι n), Finset (Y n i))
    (hsize : ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ i : ι n, M ≤ Fintype.card (Y n i))
    (hremoved : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ i : ι n,
      ((Finset.univ \ V n i).card : ℝ) ≤ δ * Fintype.card (Y n i)) :
    ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ i : ι n,
      M ≤ Fintype.card (subsetModel (Y n i) (V n i)) := by
  intro M
  obtain ⟨N₁, hN₁⟩ := hsize (2 * M)
  obtain ⟨N₂, hN₂⟩ := hremoved (1 / 2) (by norm_num)
  refine ⟨max N₁ N₂, fun n hn i ↦ ?_⟩
  have h₁ : ((2 * M : ℕ) : ℝ) ≤ Fintype.card (Y n i) := by
    exact_mod_cast hN₁ n ((le_max_left _ _).trans hn) i
  have h₂ := hN₂ n ((le_max_right _ _).trans hn) i
  have h₃ : ((Finset.univ \ V n i).card : ℝ) + (V n i).card = Fintype.card (Y n i) := by
    exact_mod_cast card_sdiff_add_card (Y n i) (V n i)
  rw [card_subsetModel]
  have h₄ : (M : ℝ) ≤ (V n i).card := by
    push_cast at h₁
    linarith
  exact_mod_cast h₄

/-- **Local multiplicativity.**  If the ambient labels are uniformly locally
multiplicative and the removed proportion vanishes uniformly, then any agreeing
retained labels are uniformly locally multiplicative. -/
theorem locallyMultiplicative_subset {K : Type} [Group K] {ι : ℕ → Type}
    {Y : ∀ n, ι n → FiniteModel} (V : ∀ n (i : ι n), Finset (Y n i))
    (act : ∀ n (i : ι n), K → Equiv.Perm (Y n i))
    (ract : ∀ n (i : ι n), K → Equiv.Perm (subsetModel (Y n i) (V n i)))
    (hagree : ∀ n (i : ι n) (g : K) (x : subsetModel (Y n i) (V n i)),
      act n i g (x : Y n i) ∈ V n i → (ract n i g x : Y n i) = act n i g x)
    (hmult : ∀ (g h : K) (δ : ℝ), 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ i : ι n,
      hammingDistance (Y n i) (act n i (g * h)) (act n i g * act n i h) < δ)
    (hremoved : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ i : ι n,
      ((Finset.univ \ V n i).card : ℝ) ≤ δ * Fintype.card (Y n i)) :
    ∀ (g h : K) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ i : ι n,
      hammingDistance (subsetModel (Y n i) (V n i)) (ract n i (g * h))
        (ract n i g * ract n i h) < ε := by
  intro g h ε hε
  obtain ⟨N₁, hN₁⟩ := hmult g h (ε / 4) (by positivity)
  obtain ⟨N₂, hN₂⟩ := hremoved (ε / 16) (by positivity)
  obtain ⟨N₃, hN₃⟩ := hremoved (1 / 2) (by norm_num)
  refine ⟨max N₁ (max N₂ N₃), fun n hn i ↦ ?_⟩
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : N₂ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn₃ : N₃ ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  have hamb := hN₁ n hn₁ i
  have hb₁ := hN₂ n hn₂ i
  have hb₂ := hN₃ n hn₃ i
  have hcount : ((hammingDisagreement (ract n i (g * h)) (ract n i g * ract n i h)).card : ℝ) ≤
      (hammingDisagreement (act n i (g * h)) (act n i g * act n i h)).card +
        3 * (Finset.univ \ V n i).card := by
    exact_mod_cast card_hammingDisagreement_subset_mul_le (V n i) (act n i) (ract n i)
      (hagree n i) g h
  have hsplit : ((Finset.univ \ V n i).card : ℝ) + (V n i).card = Fintype.card (Y n i) := by
    exact_mod_cast card_sdiff_add_card (Y n i) (V n i)
  have hb0 : (0 : ℝ) ≤ (Finset.univ \ V n i).card := Nat.cast_nonneg _
  unfold hammingDistance at hamb ⊢
  rw [card_subsetModel]
  rcases Nat.eq_zero_or_pos (V n i).card with hv0 | hvpos
  · rw [hv0, Nat.cast_zero, div_zero]
    exact hε
  · have hvR : (0 : ℝ) < (V n i).card := by exact_mod_cast hvpos
    have hyR : (0 : ℝ) < Fintype.card (Y n i) := by linarith
    rw [div_lt_iff₀ hvR]
    rw [div_lt_iff₀ hyR] at hamb
    have hyv : (Fintype.card (Y n i) : ℝ) ≤ 2 * (V n i).card := by linarith
    have hεyv : ε * (Fintype.card (Y n i) : ℝ) ≤ ε * (2 * (V n i).card) :=
      mul_le_mul_of_nonneg_left hyv hε.le
    have hεv : 0 < ε * ((V n i).card : ℝ) := mul_pos hε hvR
    linarith

/-- **Injective labels.**  Suppose that ambient labels of distinct elements of
a finite set `T` eventually collide on at most a quarter of each model, at most
an eighth of each model is eventually removed, and the models are eventually
nonempty.  Then any agreeing retained labels are eventually injective on `T`. -/
theorem labelsInjective_subset {K : Type} [Group K] (T : Finset K) {ι : ℕ → Type}
    {Y : ∀ n, ι n → FiniteModel} (V : ∀ n (i : ι n), Finset (Y n i))
    (act : ∀ n (i : ι n), K → Equiv.Perm (Y n i))
    (ract : ∀ n (i : ι n), K → Equiv.Perm (subsetModel (Y n i) (V n i)))
    (hagree : ∀ n (i : ι n) (g : K) (x : subsetModel (Y n i) (V n i)),
      act n i g (x : Y n i) ∈ V n i → (ract n i g x : Y n i) = act n i g x)
    (hcollision : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → ∃ N : ℕ, ∀ n ≥ N, ∀ i : ι n,
      ((Finset.univ.filter fun y : Y n i ↦ act n i t y = act n i t' y).card : ℝ) ≤
        1 / 4 * Fintype.card (Y n i))
    (hremoved : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ i : ι n,
      ((Finset.univ \ V n i).card : ℝ) ≤ δ * Fintype.card (Y n i))
    (hpos : ∃ N : ℕ, ∀ n ≥ N, ∀ i : ι n, 0 < Fintype.card (Y n i)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ i : ι n, Set.InjOn (ract n i) (T : Set K) := by
  have hev : ∀ p ∈ T ×ˢ T, ∃ N : ℕ, ∀ n ≥ N, p.1 ≠ p.2 → ∀ i : ι n,
      ((Finset.univ.filter fun y : Y n i ↦ act n i p.1 y = act n i p.2 y).card : ℝ) ≤
        1 / 4 * Fintype.card (Y n i) := by
    intro p hp
    obtain ⟨ht, ht'⟩ := Finset.mem_product.mp hp
    by_cases hne : p.1 = p.2
    · exact ⟨0, fun _ _ h ↦ absurd hne h⟩
    · obtain ⟨N, hN⟩ := hcollision p.1 ht p.2 ht' hne
      exact ⟨N, fun n hn _ ↦ hN n hn⟩
  obtain ⟨Nc, hNc⟩ := eventually_finset (T ×ˢ T) _ hev
  obtain ⟨Nr, hNr⟩ := hremoved (1 / 8) (by norm_num)
  obtain ⟨Np, hNp⟩ := hpos
  refine ⟨max Nc (max Nr Np), fun n hn i t ht t' ht' heq ↦ ?_⟩
  have hnc : Nc ≤ n := (le_max_left _ _).trans hn
  have hnr : Nr ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hnp : Np ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  by_contra hne
  have hcoll : ((Finset.univ.filter fun y : Y n i ↦ act n i t y = act n i t' y).card : ℝ) ≤
      1 / 4 * Fintype.card (Y n i) :=
    hNc n hnc (t, t') (Finset.mem_product.mpr ⟨ht, ht'⟩) hne i
  have hrem := hNr n hnr i
  have hposR : (0 : ℝ) < Fintype.card (Y n i) := by exact_mod_cast hNp n hnp i
  have hcount : ((V n i).card : ℝ) ≤
      (Finset.univ.filter fun y : Y n i ↦ act n i t y = act n i t' y).card +
        2 * (Finset.univ \ V n i).card := by
    exact_mod_cast card_le_collision_add_of_subset_eq (V n i) (act n i t) (act n i t')
      (ract n i t) (ract n i t') (hagree n i t) (hagree n i t') heq
  have hsplit : ((Finset.univ \ V n i).card : ℝ) + (V n i).card = Fintype.card (Y n i) := by
    exact_mod_cast card_sdiff_add_card (Y n i) (V n i)
  linarith

/-! ## Completed component labels -/

/-- **Collisions of completed labels.**  On an expander component, two completed
labels agree only at ambient collisions or where one of the two ambient images
leaves the component. -/
theorem card_componentCompletedAction_collision_le {K : Type} [Group K]
    {S : SoficApproximation K} {T : Finset K} (D : ExpanderDecomposition S T) (n : ℕ)
    (C : D.componentIndex n) (t t' : K) :
    (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
        D.componentCompletedAction n C t x = D.componentCompletedAction n C t' x).card ≤
      (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n t (x : S.model n) = S.map n t' (x : S.model n)).card +
        (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n t (x : S.model n) ∉ C.block).card +
        (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n t' (x : S.model n) ∉ C.block).card := by
  have hsub : (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
        D.componentCompletedAction n C t x = D.componentCompletedAction n C t' x) ⊆
      (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n t (x : S.model n) = S.map n t' (x : S.model n)) ∪
        (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n t (x : S.model n) ∉ C.block) ∪
        (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n t' (x : S.model n) ∉ C.block) := by
    intro x hx
    have heq : D.componentCompletedAction n C t x = D.componentCompletedAction n C t' x :=
      (Finset.mem_filter.mp hx).2
    by_cases hx₁ : S.map n t (x : S.model n) ∈ C.block
    · by_cases hx₂ : S.map n t' (x : S.model n) ∈ C.block
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← D.componentCompletedAction_agrees n C t x hx₁,
          ← D.componentCompletedAction_agrees n C t' x hx₂, heq]
      · apply Finset.mem_union_right
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hx₂
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hx₁
  have hcard := Finset.card_le_card hsub
  have hu₁ := Finset.card_union_le
    ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n t (x : S.model n) = S.map n t' (x : S.model n)) ∪
        (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n t (x : S.model n) ∉ C.block))
    (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n t' (x : S.model n) ∉ C.block)
  have hu₂ := Finset.card_union_le
    (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n t (x : S.model n) = S.map n t' (x : S.model n))
    (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n t (x : S.model n) ∉ C.block)
  omega

end ComponentFamilyUniformFields
end GroupApproximation
