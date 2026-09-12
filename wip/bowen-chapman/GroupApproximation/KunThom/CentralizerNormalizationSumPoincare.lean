import GroupApproximation.KunThom.CentralizerNormalizationFiberCoarea
import GroupApproximation.Matching.PartialBijectionSwap

/-!
# The coarea inequalities on a disjoint union of two expanders

A disjoint union `X ⊕ Z` carrying summand-preserving labels is never an
expander: `X` itself has empty boundary.  The median-one Poincaré inequality
therefore fails on the union for general functions.  It still holds for
functions that have median one on each summand separately, because the
label variation on the union dominates the sum of the variations on the two
summands.

A relation that is close to the graph of a permutation of the union has at
most as many bad rows and bad columns as edits.  When the edits are fewer
than half of each summand, the row and column multiplicities have median one
on each summand, and the two coarea inequalities used by singleton-core
rounding follow (`fiberCoarea_sum`).
-/

namespace GroupApproximation
namespace CentralizerNormalizationSumPoincare

open AlmostAutomorphism
open KazhdanImprovement
open CentralizerNormalizationFiberCoarea
open FinitePartialBijection (sumModel)

variable {X Z : FiniteModel}

/-- The left component of a permutation of the disjoint union, read through
the injective homomorphism `Equiv.Perm.sumCongrHom`.  It is meaningful for
summand-preserving permutations. -/
noncomputable def leftPart (σ : Equiv.Perm (sumModel X Z)) : Equiv.Perm X :=
  (Function.invFun (Equiv.Perm.sumCongrHom X Z) σ).1

/-- The right component of a permutation of the disjoint union. -/
noncomputable def rightPart (σ : Equiv.Perm (sumModel X Z)) : Equiv.Perm Z :=
  (Function.invFun (Equiv.Perm.sumCongrHom X Z) σ).2

theorem invFun_sumCongrHom_sumCongr (a : Equiv.Perm X) (b : Equiv.Perm Z) :
    Function.invFun (Equiv.Perm.sumCongrHom X Z) (Equiv.sumCongr a b) = (a, b) := by
  have h := Function.leftInverse_invFun
    (Equiv.Perm.sumCongrHom_injective (α := X) (β := Z)) (a, b)
  simpa only [Equiv.Perm.sumCongrHom_apply] using h

@[simp] theorem leftPart_sumCongr (a : Equiv.Perm X) (b : Equiv.Perm Z) :
    leftPart (X := X) (Z := Z) (Equiv.sumCongr a b) = a := by
  unfold leftPart
  rw [invFun_sumCongrHom_sumCongr]

@[simp] theorem rightPart_sumCongr (a : Equiv.Perm X) (b : Equiv.Perm Z) :
    rightPart (X := X) (Z := Z) (Equiv.sumCongr a b) = b := by
  unfold rightPart
  rw [invFun_sumCongrHom_sumCongr]

/-- A summand-preserving permutation acts on the left summand by its left
part. -/
theorem apply_inl_of_eq_sumCongr {σ : Equiv.Perm (sumModel X Z)}
    (hσ : σ = Equiv.sumCongr (leftPart σ) (rightPart σ)) (x : X) :
    σ (Sum.inl x) = Sum.inl (leftPart σ x) := by
  have h := congrArg (fun τ : Equiv.Perm (sumModel X Z) ↦ τ (Sum.inl x)) hσ
  simpa using h

/-- A summand-preserving permutation acts on the right summand by its right
part. -/
theorem apply_inr_of_eq_sumCongr {σ : Equiv.Perm (sumModel X Z)}
    (hσ : σ = Equiv.sumCongr (leftPart σ) (rightPart σ)) (z : Z) :
    σ (Sum.inr z) = Sum.inr (rightPart σ z) := by
  have h := congrArg (fun τ : Equiv.Perm (sumModel X Z) ↦ τ (Sum.inr z)) hσ
  simpa using h

/-- The label variation, summed label by label. -/
theorem natLabelVariation_eq_sum (Y : FiniteModel) (S : Finset (Equiv.Perm Y))
    (g : Y → ℕ) :
    natLabelVariation Y S g = ∑ σ ∈ S, ∑ y : Y, Nat.dist (g y) (g (σ y)) := by
  unfold natLabelVariation
  exact Finset.sum_product S (Finset.univ : Finset Y)
    (fun p : Equiv.Perm Y × Y ↦ Nat.dist (g p.2) (g (p.1 p.2)))

open Classical in
/-- The variation on the union dominates the variations on the two summands,
for the left and right parts of the union's labels. -/
theorem natLabelVariation_summands_le
    (SW : Finset (Equiv.Perm (sumModel X Z)))
    (hpreserve : ∀ σ ∈ SW, σ = Equiv.sumCongr (leftPart σ) (rightPart σ))
    (g : sumModel X Z → ℕ) :
    natLabelVariation X (SW.image leftPart) (fun x ↦ g (Sum.inl x)) +
        natLabelVariation Z (SW.image rightPart) (fun z ↦ g (Sum.inr z)) ≤
      natLabelVariation (sumModel X Z) SW g := by
  classical
  rw [natLabelVariation_eq_sum, natLabelVariation_eq_sum, natLabelVariation_eq_sum]
  have hleft :
      (∑ a ∈ SW.image leftPart, ∑ x : X, Nat.dist (g (Sum.inl x)) (g (Sum.inl (a x)))) ≤
        ∑ σ ∈ SW, ∑ x : X, Nat.dist (g (Sum.inl x)) (g (σ (Sum.inl x))) := by
    refine (Finset.sum_image_le_of_nonneg (fun _ _ ↦ Nat.zero_le _)).trans ?_
    refine le_of_eq (Finset.sum_congr rfl fun σ hσ ↦ Finset.sum_congr rfl fun x _ ↦ ?_)
    rw [apply_inl_of_eq_sumCongr (hpreserve σ hσ) x]
  have hright :
      (∑ b ∈ SW.image rightPart, ∑ z : Z, Nat.dist (g (Sum.inr z)) (g (Sum.inr (b z)))) ≤
        ∑ σ ∈ SW, ∑ z : Z, Nat.dist (g (Sum.inr z)) (g (σ (Sum.inr z))) := by
    refine (Finset.sum_image_le_of_nonneg (fun _ _ ↦ Nat.zero_le _)).trans ?_
    refine le_of_eq (Finset.sum_congr rfl fun σ hσ ↦ Finset.sum_congr rfl fun z _ ↦ ?_)
    rw [apply_inr_of_eq_sumCongr (hpreserve σ hσ) z]
  have hsplit :
      (∑ σ ∈ SW, ∑ w : sumModel X Z, Nat.dist (g w) (g (σ w))) =
        (∑ σ ∈ SW, ∑ x : X, Nat.dist (g (Sum.inl x)) (g (σ (Sum.inl x)))) +
          ∑ σ ∈ SW, ∑ z : Z, Nat.dist (g (Sum.inr z)) (g (σ (Sum.inr z))) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ ↦
      Fintype.sum_sum_type (fun w : sumModel X Z ↦ Nat.dist (g w) (g (σ w)))
  rw [hsplit]
  exact add_le_add hleft hright

open Classical in
/-- The median-one Poincaré inequality on the union, for functions with
median one on each summand. -/
theorem mul_sum_dist_one_le_natLabelVariation
    (SW : Finset (Equiv.Perm (sumModel X Z)))
    (hpreserve : ∀ σ ∈ SW, σ = Equiv.sumCongr (leftPart σ) (rightPart σ))
    {h : ℝ}
    (hX : HasL1PoincareAtOne X (SW.image leftPart) h)
    (hZ : HasL1PoincareAtOne Z (SW.image rightPart) h)
    (g : sumModel X Z → ℕ)
    (hlowX : 2 * (Finset.univ.filter fun x : X ↦ g (Sum.inl x) < 1).card ≤
      Fintype.card X)
    (hupX : 2 * (Finset.univ.filter fun x : X ↦ 1 < g (Sum.inl x)).card ≤
      Fintype.card X)
    (hlowZ : 2 * (Finset.univ.filter fun z : Z ↦ g (Sum.inr z) < 1).card ≤
      Fintype.card Z)
    (hupZ : 2 * (Finset.univ.filter fun z : Z ↦ 1 < g (Sum.inr z)).card ≤
      Fintype.card Z) :
    h * ((∑ w : sumModel X Z, Nat.dist (g w) 1 : ℕ) : ℝ) ≤
      (natLabelVariation (sumModel X Z) SW g : ℝ) := by
  have hXg := hX.2 (fun x ↦ g (Sum.inl x)) hlowX hupX
  have hZg := hZ.2 (fun z ↦ g (Sum.inr z)) hlowZ hupZ
  have hsplit :
      (∑ w : sumModel X Z, Nat.dist (g w) 1) =
        (∑ x : X, Nat.dist (g (Sum.inl x)) 1) + ∑ z : Z, Nat.dist (g (Sum.inr z)) 1 :=
    Fintype.sum_sum_type (fun w : sumModel X Z ↦ Nat.dist (g w) 1)
  have hvar := natLabelVariation_summands_le SW hpreserve g
  have hvarReal :
      (natLabelVariation X (SW.image leftPart) (fun x ↦ g (Sum.inl x)) : ℝ) +
          (natLabelVariation Z (SW.image rightPart) (fun z ↦ g (Sum.inr z)) : ℝ) ≤
        (natLabelVariation (sumModel X Z) SW g : ℝ) := by
    exact_mod_cast hvar
  rw [hsplit, Nat.cast_add]
  linarith

/-- Bad rows lying over the left summand are bad rows of the union. -/
theorem card_left_filter_rowDegree_ne_one_le
    (U : Finset (sumModel X Z × sumModel X Z)) :
    (Finset.univ.filter fun x : X ↦ rowDegree (sumModel X Z) U (Sum.inl x) ≠ 1).card ≤
      (badRows (sumModel X Z) U).card := by
  classical
  rw [← Finset.card_image_of_injective _ Sum.inl_injective]
  refine Finset.card_le_card fun w hw ↦ ?_
  rw [Finset.mem_image] at hw
  obtain ⟨x, hx, rfl⟩ := hw
  rw [Finset.mem_filter] at hx
  rw [mem_badRows]
  exact hx.2

/-- Bad rows lying over the right summand are bad rows of the union. -/
theorem card_right_filter_rowDegree_ne_one_le
    (U : Finset (sumModel X Z × sumModel X Z)) :
    (Finset.univ.filter fun z : Z ↦ rowDegree (sumModel X Z) U (Sum.inr z) ≠ 1).card ≤
      (badRows (sumModel X Z) U).card := by
  classical
  rw [← Finset.card_image_of_injective _ Sum.inr_injective]
  refine Finset.card_le_card fun w hw ↦ ?_
  rw [Finset.mem_image] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  rw [Finset.mem_filter] at hz
  rw [mem_badRows]
  exact hz.2

/-- Bad columns lying over the left summand are bad columns of the union. -/
theorem card_left_filter_columnDegree_ne_one_le
    (U : Finset (sumModel X Z × sumModel X Z)) :
    (Finset.univ.filter fun x : X ↦ columnDegree (sumModel X Z) U (Sum.inl x) ≠ 1).card ≤
      (badColumns (sumModel X Z) U).card := by
  classical
  rw [← Finset.card_image_of_injective _ Sum.inl_injective]
  refine Finset.card_le_card fun w hw ↦ ?_
  rw [Finset.mem_image] at hw
  obtain ⟨x, hx, rfl⟩ := hw
  rw [Finset.mem_filter] at hx
  rw [mem_badColumns]
  exact hx.2

/-- Bad columns lying over the right summand are bad columns of the union. -/
theorem card_right_filter_columnDegree_ne_one_le
    (U : Finset (sumModel X Z × sumModel X Z)) :
    (Finset.univ.filter fun z : Z ↦ columnDegree (sumModel X Z) U (Sum.inr z) ≠ 1).card ≤
      (badColumns (sumModel X Z) U).card := by
  classical
  rw [← Finset.card_image_of_injective _ Sum.inr_injective]
  refine Finset.card_le_card fun w hw ↦ ?_
  rw [Finset.mem_image] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  rw [Finset.mem_filter] at hz
  rw [mem_badColumns]
  exact hz.2

/-- Levels below and above one are contained in the bad set. -/
theorem card_filter_lt_one_le_ne_one {ι : Type*} [Fintype ι] (g : ι → ℕ) :
    (Finset.univ.filter fun i ↦ g i < 1).card ≤
      (Finset.univ.filter fun i ↦ g i ≠ 1).card := by
  classical
  refine Finset.card_le_card fun i hi ↦ ?_
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, by omega⟩

theorem card_filter_one_lt_le_ne_one {ι : Type*} [Fintype ι] (g : ι → ℕ) :
    (Finset.univ.filter fun i ↦ 1 < g i).card ≤
      (Finset.univ.filter fun i ↦ g i ≠ 1).card := by
  classical
  refine Finset.card_le_card fun i hi ↦ ?_
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, by omega⟩

open Classical in
/-- **The two coarea inequalities on a disjoint union.**  If each summand has
the median-one Poincaré inequality for the parts of the labels, and a relation
differs from the graph of a permutation of the union by fewer edits than half
of each summand, then singleton-core rounding applies to the relation. -/
theorem fiberCoarea_sum
    (SW : Finset (Equiv.Perm (sumModel X Z)))
    (hpreserve : ∀ σ ∈ SW, σ = Equiv.sumCongr (leftPart σ) (rightPart σ))
    {h : ℝ}
    (hX : HasL1PoincareAtOne X (SW.image leftPart) h)
    (hZ : HasL1PoincareAtOne Z (SW.image rightPart) h)
    (U : Finset (sumModel X Z × sumModel X Z)) (c : Equiv.Perm (sumModel X Z))
    (heditsX : 2 * ((permutationGraph (sumModel X Z) c \ U).card +
      (U \ permutationGraph (sumModel X Z) c).card) ≤ Fintype.card X)
    (heditsZ : 2 * ((permutationGraph (sumModel X Z) c \ U).card +
      (U \ permutationGraph (sumModel X Z) c).card) ≤ Fintype.card Z) :
    FiberCoarea (sumModel X Z) SW U h := by
  have hrowsBad := card_badRows_le_edits (sumModel X Z) U c
  have hcolumnsBad := card_badColumns_le_edits (sumModel X Z) U c
  have hlX := card_left_filter_rowDegree_ne_one_le U
  have hrZ := card_right_filter_rowDegree_ne_one_le U
  have hclX := card_left_filter_columnDegree_ne_one_le U
  have hcrZ := card_right_filter_columnDegree_ne_one_le U
  have hrowLowX := card_filter_lt_one_le_ne_one
    (fun x : X ↦ rowDegree (sumModel X Z) U (Sum.inl x))
  have hrowUpX := card_filter_one_lt_le_ne_one
    (fun x : X ↦ rowDegree (sumModel X Z) U (Sum.inl x))
  have hrowLowZ := card_filter_lt_one_le_ne_one
    (fun z : Z ↦ rowDegree (sumModel X Z) U (Sum.inr z))
  have hrowUpZ := card_filter_one_lt_le_ne_one
    (fun z : Z ↦ rowDegree (sumModel X Z) U (Sum.inr z))
  have hcolLowX := card_filter_lt_one_le_ne_one
    (fun x : X ↦ columnDegree (sumModel X Z) U (Sum.inl x))
  have hcolUpX := card_filter_one_lt_le_ne_one
    (fun x : X ↦ columnDegree (sumModel X Z) U (Sum.inl x))
  have hcolLowZ := card_filter_lt_one_le_ne_one
    (fun z : Z ↦ columnDegree (sumModel X Z) U (Sum.inr z))
  have hcolUpZ := card_filter_one_lt_le_ne_one
    (fun z : Z ↦ columnDegree (sumModel X Z) U (Sum.inr z))
  refine ⟨hX.1, ?_, ?_⟩
  · have hcoarea := mul_sum_dist_one_le_natLabelVariation SW hpreserve hX hZ
      (rowDegree (sumModel X Z) U)
      (by omega) (by omega) (by omega) (by omega)
    have hvariation := rowDegreeVariation_le_relationBoundary (sumModel X Z) SW U
    have hvariationReal :
        (natLabelVariation (sumModel X Z) SW (rowDegree (sumModel X Z) U) : ℝ) ≤
          ((relationBoundary (sumModel X Z) SW U).card : ℝ) := by
      exact_mod_cast hvariation
    exact hcoarea.trans hvariationReal
  · have hcoarea := mul_sum_dist_one_le_natLabelVariation SW hpreserve hX hZ
      (columnDegree (sumModel X Z) U)
      (by omega) (by omega) (by omega) (by omega)
    have hvariation := columnDegreeVariation_le_relationBoundary (sumModel X Z) SW U
    have hvariationReal :
        (natLabelVariation (sumModel X Z) SW (columnDegree (sumModel X Z) U) : ℝ) ≤
          ((relationBoundary (sumModel X Z) SW U).card : ℝ) := by
      exact_mod_cast hvariation
    exact hcoarea.trans hvariationReal

end CentralizerNormalizationSumPoincare
end GroupApproximation
