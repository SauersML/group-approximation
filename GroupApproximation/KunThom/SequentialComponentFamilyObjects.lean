import GroupApproximation.KunThom.SequentialComponentFamilyLevels

/-!
# Objects of the sequential component family

The objects at index `n` are the components that are good at the diagonal level
(`objectIndex`).  An object carries the pruned points of its component
(`objectModel`) and the completed labels there (`objectAction`).  This module
proves the four properties that the uniform improvement of candidates consumes.

* `objectAction_expands`: every object has directed Cheeger constant
  `h / (8 |T|)` for the labels of `T`.
* `objectModel_size`: object sizes tend to infinity uniformly.
* `objectAction_locallyMultiplicative`: for fixed `g, h`, the normalized product
  failure tends to zero uniformly over objects.
* `objectAction_injOn`: eventually the labels of `T` are distinct on every object.

`objectEmbedding` places an object in the ambient model, and
`card_objectAction_disagreement_le` bounds where its labels differ from the
ambient permutations.
-/

namespace GroupApproximation
namespace SequentialComponentFamily

open scoped BigOperators

variable {K : Type} [Group K] {S : SoficApproximation K} {T : Finset K}
variable (D : ExpanderDecomposition S T)

open Classical in
/-- The components that are good at the diagonal level. -/
abbrev objectIndex (enum : ℕ → K) (n : ℕ) : Type :=
  {C : D.componentIndex n // IsGoodAt D enum (level D enum n) n C}

/-- The pruned points of an object. -/
noncomputable abbrev objectModel (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ)
    (i : objectIndex D enum n) : FiniteModel :=
  finsetModel (indexedBlockModel (D.blocks n) i.1) (Finset.univ \ prunedSet D hT n i.1)

/-- The completed labels of an object. -/
noncomputable def objectAction (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ)
    (i : objectIndex D enum n) (g : K) : Equiv.Perm (objectModel D hT enum n i) :=
  completion (Finset.univ \ prunedSet D hT n i.1) (D.componentCompletedAction n i.1 g)

/-- An object inside the ambient model. -/
def objectEmbedding (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ) (i : objectIndex D enum n)
    (y : objectModel D hT enum n i) : S.model n :=
  ((y : indexedBlockModel (D.blocks n) i.1) : S.model n)

theorem objectEmbedding_injective (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ)
    (i : objectIndex D enum n) : Function.Injective (objectEmbedding D hT enum n i) := by
  intro y z hyz
  exact Subtype.ext (Subtype.ext hyz)

theorem objectEmbedding_mem (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ)
    (i : objectIndex D enum n) (y : objectModel D hT enum n i) :
    objectEmbedding D hT enum n i y ∈ i.1.block :=
  (y : indexedBlockModel (D.blocks n) i.1).2

/-! ### Expansion and sizes -/

theorem objectAction_expands (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ)
    (i : objectIndex D enum n) :
    DirectedCoarea.HasCheegerLowerBound (objectModel D hT enum n i)
      (T.image (objectAction D hT enum n i)) (D.cheeger / (8 * T.card)) :=
  (prunedSet_spec D hT n i.1 i.2.1).2

theorem card_objectModel (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ)
    (i : objectIndex D enum n) :
    Fintype.card (objectModel D hT enum n i) =
      i.1.block.card - (prunedSet D hT n i.1).card := by
  rw [Fintype.card_coe, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_coe]

theorem five_mul_card_prunedSet_le (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ)
    (i : objectIndex D enum n) :
    5 * (prunedSet D hT n i.1).card ≤ i.1.block.card := by
  have h := (prunedSet_spec D hT n i.1 i.2.1).1
  have hgood := i.2.1
  have hc := D.cheeger_pos
  have hreal : D.cheeger * (5 * (prunedSet D hT n i.1).card : ℝ) ≤
      D.cheeger * i.1.block.card := by
    linarith
  have h5 := le_of_mul_le_mul_left hreal hc
  exact_mod_cast h5

theorem objectModel_size [Infinite K] (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set K) = ⊤) (hT : T.Nonempty) (enum : ℕ → K) (M : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ i : objectIndex D enum n,
      M ≤ Fintype.card (objectModel D hT enum n i) := by
  obtain ⟨N, hN⟩ := level_diverges D hsymm hgen enum (2 * M)
  refine ⟨N, fun n hn i ↦ ?_⟩
  have hk := hN n hn
  have hlt := i.2.2.2
  have h5 := five_mul_card_prunedSet_le D hT enum n i
  rw [card_objectModel]
  omega

/-! ### Product law -/

theorem objectAction_locallyMultiplicative [Infinite K] (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set K) = ⊤) (hT : T.Nonempty) (enum : ℕ → K)
    (henum : Function.Surjective enum) (g h : K) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ i : objectIndex D enum n,
      hammingDistance (objectModel D hT enum n i) (objectAction D hT enum n i (g * h))
        (objectAction D hT enum n i g * objectAction D hT enum n i h) < ε := by
  obtain ⟨a, rfl⟩ := henum g
  obtain ⟨b, rfl⟩ := henum h
  obtain ⟨k₁, hk₁⟩ := exists_nat_gt (10 / ε)
  obtain ⟨N, hN⟩ := level_diverges D hsymm hgen enum (max (max (a + 1) (b + 1)) k₁)
  refine ⟨N, fun n hn i ↦ ?_⟩
  have hkge := hN n hn
  have hak : a < level D enum n := (le_max_left _ _).trans ((le_max_left _ _).trans hkge)
  have hbk : b < level D enum n := (le_max_right _ _).trans ((le_max_left _ _).trans hkge)
  have hk₁k : k₁ ≤ level D enum n := (le_max_right _ _).trans hkge
  -- counts
  have hmerr : (hammingDisagreement (objectAction D hT enum n i (enum a * enum b))
      (objectAction D hT enum n i (enum a) * objectAction D hT enum n i (enum b))).card ≤
      (D.componentMultiplicationError n i.1 (enum a) (enum b)).card +
        3 * (prunedSet D hT n i.1).card :=
    card_completion_multiplicationError_le (D.componentCompletedAction n i.1)
      (prunedSet D hT n i.1) (enum a) (enum b)
  have h5 := five_mul_card_prunedSet_le D hT enum n i
  have hlt := i.2.2.2
  have hcardObj := card_objectModel D hT enum n i
  -- real facts
  have hmerrR : ((hammingDisagreement (objectAction D hT enum n i (enum a * enum b))
      (objectAction D hT enum n i (enum a) * objectAction D hT enum n i (enum b))).card : ℝ) ≤
      (D.componentMultiplicationError n i.1 (enum a) (enum b)).card +
        3 * ((prunedSet D hT n i.1).card : ℝ) := by
    exact_mod_cast hmerr
  have hmem : (a, b) ∈ Finset.range (level D enum n) ×ˢ Finset.range (level D enum n) :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr hak, Finset.mem_range.mpr hbk⟩
  have hsingle : ((D.componentMultiplicationError n i.1 (enum a) (enum b)).card : ℝ) ≤
      multError D enum (level D enum n) n i.1 := by
    unfold multError
    exact Finset.single_le_sum
      (s := Finset.range (level D enum n) ×ˢ Finset.range (level D enum n))
      (f := fun p : ℕ × ℕ ↦
        ((D.componentMultiplicationError n i.1 (enum p.1) (enum p.2)).card : ℝ))
      (fun _ _ ↦ Nat.cast_nonneg _) (a := (a, b)) hmem
  have hM0 : (0 : ℝ) ≤ (D.componentMultiplicationError n i.1 (enum a) (enum b)).card :=
    Nat.cast_nonneg _
  have hdis : 0 ≤ disError D n i.1 := by
    unfold disError
    exact Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hcoll : 0 ≤ collError D n i.1 := by
    unfold collError
    exact Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hE : levelError D enum (level D enum n) n i.1 =
      multError D enum (level D enum n) n i.1 + disError D n i.1 + collError D n i.1 +
        D.cheeger⁻¹ * D.componentLabelEditBudget n i.1 := by
    simp only [levelError]
  have hEnonneg := levelError_nonneg D enum (level D enum n) n i.1
  have hU := card_prunedSet_le D hT n i.1 i.2.1
  have hgoodE := i.2.2.1
  have hk₁R : (10 : ℝ) / ε < level D enum n :=
    hk₁.trans_le (by exact_mod_cast hk₁k)
  have hkε : 10 < ε * (level D enum n : ℝ) := by
    rw [div_lt_iff₀ hε] at hk₁R
    linarith
  have hs4 : 10 * levelError D enum (level D enum n) n i.1 ≤
      ε * ((level D enum n : ℝ) + 1) * levelError D enum (level D enum n) n i.1 := by
    apply mul_le_mul_of_nonneg_right _ hEnonneg
    linarith
  have hs3 : ε * (((level D enum n : ℝ) + 1) * levelError D enum (level D enum n) n i.1) ≤
      ε * i.1.block.card :=
    mul_le_mul_of_nonneg_left hgoodE hε.le
  have h5R : (5 * (prunedSet D hT n i.1).card : ℝ) ≤ i.1.block.card := by exact_mod_cast h5
  have hs6 : ε * (5 * ((prunedSet D hT n i.1).card : ℝ)) ≤ ε * i.1.block.card :=
    mul_le_mul_of_nonneg_left h5R hε.le
  have hCpos : (0 : ℝ) < i.1.block.card := by
    have hpos : 0 < i.1.block.card := by omega
    exact_mod_cast hpos
  have hεC : 0 < ε * (i.1.block.card : ℝ) := mul_pos hε hCpos
  have hUle : (prunedSet D hT n i.1).card ≤ i.1.block.card := by omega
  have hcardR : (Fintype.card (objectModel D hT enum n i) : ℝ) =
      i.1.block.card - (prunedSet D hT n i.1).card := by
    rw [hcardObj, Nat.cast_sub hUle]
  have hobjpos : (0 : ℝ) < Fintype.card (objectModel D hT enum n i) := by
    rw [hcardR]
    linarith
  rw [hammingDistance, div_lt_iff₀ hobjpos, hcardR]
  have hB := budget_div_nonneg D n i.1
  linarith

/-! ### Distinct labels -/

theorem objectAction_injOn [Infinite K] (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set K) = ⊤) (hT : T.Nonempty) (enum : ℕ → K) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ i : objectIndex D enum n,
      Set.InjOn (objectAction D hT enum n i) (T : Set K) := by
  classical
  obtain ⟨N, hN⟩ := level_diverges D hsymm hgen enum 9
  refine ⟨N, fun n hn i ↦ ?_⟩
  intro s hs t ht hst
  by_contra hne
  have hk : 9 ≤ level D enum n := hN n hn
  have hcollision := card_sub_le_collision_add_of_completion_eq (prunedSet D hT n i.1)
    (D.componentCompletedAction n i.1 s) (D.componentCompletedAction n i.1 t) hst
  rw [Fintype.card_coe] at hcollision
  have hsub : (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) i.1 ↦
      D.componentCompletedAction n i.1 s x = D.componentCompletedAction n i.1 t x) ⊆
      D.componentCompletionDisagreement n i.1 s ∪ D.componentCompletionDisagreement n i.1 t ∪
        componentCollision D n i.1 s t := by
    intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    simp only [ExpanderDecomposition.componentCompletionDisagreement, componentCollision,
      Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hnot
    simp only [not_or, not_not] at hnot
    obtain ⟨⟨h1, h2⟩, h3⟩ := hnot
    apply h3
    rw [← h1, ← h2, hx']
  have hsubcard := Finset.card_le_card hsub
  have u1 := Finset.card_union_le
    (D.componentCompletionDisagreement n i.1 s ∪ D.componentCompletionDisagreement n i.1 t)
    (componentCollision D n i.1 s t)
  have u2 := Finset.card_union_le (D.componentCompletionDisagreement n i.1 s)
    (D.componentCompletionDisagreement n i.1 t)
  have h5 := five_mul_card_prunedSet_le D hT enum n i
  have hnat : i.1.block.card ≤ (D.componentCompletionDisagreement n i.1 s).card +
      (D.componentCompletionDisagreement n i.1 t).card +
        (componentCollision D n i.1 s t).card + 3 * (prunedSet D hT n i.1).card := by
    omega
  have hnatR : (i.1.block.card : ℝ) ≤ (D.componentCompletionDisagreement n i.1 s).card +
      (D.componentCompletionDisagreement n i.1 t).card +
        (componentCollision D n i.1 s t).card + 3 * ((prunedSet D hT n i.1).card : ℝ) := by
    exact_mod_cast hnat
  have hdis_s : ((D.componentCompletionDisagreement n i.1 s).card : ℝ) ≤ disError D n i.1 := by
    unfold disError
    exact Finset.single_le_sum
      (f := fun g : K ↦ ((D.componentCompletionDisagreement n i.1 g).card : ℝ))
      (fun _ _ ↦ Nat.cast_nonneg _) (a := s) hs
  have hdis_t : ((D.componentCompletionDisagreement n i.1 t).card : ℝ) ≤ disError D n i.1 := by
    unfold disError
    exact Finset.single_le_sum
      (f := fun g : K ↦ ((D.componentCompletionDisagreement n i.1 g).card : ℝ))
      (fun _ _ ↦ Nat.cast_nonneg _) (a := t) ht
  have hmemOff : (s, t) ∈ T.offDiag := Finset.mem_offDiag.mpr ⟨hs, ht, hne⟩
  have hcoll_st : ((componentCollision D n i.1 s t).card : ℝ) ≤ collError D n i.1 := by
    unfold collError
    exact Finset.single_le_sum (s := T.offDiag)
      (f := fun p : K × K ↦ ((componentCollision D n i.1 p.1 p.2).card : ℝ))
      (fun _ _ ↦ Nat.cast_nonneg _) (a := (s, t)) hmemOff
  have hmult : 0 ≤ multError D enum (level D enum n) n i.1 := by
    unfold multError
    exact Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hdis0 : (0 : ℝ) ≤ (D.componentCompletionDisagreement n i.1 s).card := Nat.cast_nonneg _
  have hdis0' : (0 : ℝ) ≤ (D.componentCompletionDisagreement n i.1 t).card := Nat.cast_nonneg _
  have hcoll0 : (0 : ℝ) ≤ (componentCollision D n i.1 s t).card := Nat.cast_nonneg _
  have hE : levelError D enum (level D enum n) n i.1 =
      multError D enum (level D enum n) n i.1 + disError D n i.1 + collError D n i.1 +
        D.cheeger⁻¹ * D.componentLabelEditBudget n i.1 := by
    simp only [levelError]
  have hU := card_prunedSet_le D hT n i.1 i.2.1
  have hgoodE := i.2.2.1
  have hEnonneg := levelError_nonneg D enum (level D enum n) n i.1
  have hk9 : (9 : ℝ) ≤ level D enum n := by exact_mod_cast hk
  have hkE : 9 * levelError D enum (level D enum n) n i.1 ≤
      (level D enum n : ℝ) * levelError D enum (level D enum n) n i.1 :=
    mul_le_mul_of_nonneg_right hk9 hEnonneg
  have hlt := i.2.2.2
  have hCpos : (0 : ℝ) < i.1.block.card := by
    have hpos : 0 < i.1.block.card := by omega
    exact_mod_cast hpos
  have hB := budget_div_nonneg D n i.1
  linarith

/-! ### Agreement with the ambient model -/

theorem card_objectAction_disagreement_le (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ)
    (i : objectIndex D enum n) (g : K) :
    (Finset.univ.filter fun y : objectModel D hT enum n i ↦
      objectEmbedding D hT enum n i (objectAction D hT enum n i g y) ≠
        S.map n g (objectEmbedding D hT enum n i y)).card ≤
      (D.componentCompletionDisagreement n i.1 g).card + (prunedSet D hT n i.1).card := by
  classical
  let π := D.componentCompletedAction n i.1 g
  have hsub : (Finset.univ.filter fun y : objectModel D hT enum n i ↦
      objectEmbedding D hT enum n i (objectAction D hT enum n i g y) ≠
        S.map n g (objectEmbedding D hT enum n i y)) ⊆
      (Finset.univ.filter fun y : objectModel D hT enum n i ↦
        ((objectAction D hT enum n i g y : objectModel D hT enum n i) :
          indexedBlockModel (D.blocks n) i.1) ≠ π y) ∪
      (Finset.univ.filter fun y : objectModel D hT enum n i ↦
        (π y : S.model n) ≠ S.map n g ((y : indexedBlockModel (D.blocks n) i.1) : S.model n)) := by
    intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_contra hnot
    simp only [Finset.mem_univ, true_and, not_or, not_not] at hnot
    obtain ⟨h1, h2⟩ := hnot
    apply hy'
    show ((objectAction D hT enum n i g y : indexedBlockModel (D.blocks n) i.1) : S.model n) =
      S.map n g ((y : indexedBlockModel (D.blocks n) i.1) : S.model n)
    rw [h1]
    exact h2
  have h1 := card_completion_disagreement_le (prunedSet D hT n i.1) π
  have h2 : (Finset.univ.filter fun y : objectModel D hT enum n i ↦
      (π y : S.model n) ≠ S.map n g ((y : indexedBlockModel (D.blocks n) i.1) : S.model n)).card ≤
      (D.componentCompletionDisagreement n i.1 g).card := by
    refine Finset.card_le_card_of_injOn (fun y : objectModel D hT enum n i ↦
      (y : indexedBlockModel (D.blocks n) i.1)) ?_ ?_
    · intro y hy
      have hy' := (Finset.mem_filter.mp hy).2
      simp only [ExpanderDecomposition.componentCompletionDisagreement, Finset.coe_filter,
        Finset.mem_univ, true_and, Set.mem_setOf_eq]
      exact hy'
    · intro y _ z _ hyz
      exact Subtype.ext hyz
  have hcard := Finset.card_le_card hsub
  have hu := Finset.card_union_le
    (Finset.univ.filter fun y : objectModel D hT enum n i ↦
      ((objectAction D hT enum n i g y : objectModel D hT enum n i) :
        indexedBlockModel (D.blocks n) i.1) ≠ π y)
    (Finset.univ.filter fun y : objectModel D hT enum n i ↦
      (π y : S.model n) ≠ S.map n g ((y : indexedBlockModel (D.blocks n) i.1) : S.model n))
  have h1' : (Finset.univ.filter fun y : objectModel D hT enum n i ↦
      ((objectAction D hT enum n i g y : objectModel D hT enum n i) :
        indexedBlockModel (D.blocks n) i.1) ≠ π y).card ≤ (prunedSet D hT n i.1).card := h1
  omega

end SequentialComponentFamily
end GroupApproximation
