import NonsoficGroupsExist.Matching.ComponentCompletedMultiplicativity
import NonsoficGroupsExist.Matching.PartialSwapEquivariance
import NonsoficGroupsExist.Sofic.MultiplicativeApproximation

/-!
# Multiplicative approximations selected from two completed components

The compactness step in componentwise Kazhdan repair selects a pair of bad
components at each stage.  This file packages their disjoint-union labels as
an honest `MultiplicativeApproximation`.  Its multiplication hypothesis is
stated directly in terms of the already-defined local component error sets;
the conversion to Hamming distance is proved here by exact finite counting.
-/

namespace NonsoficGroupsExist
namespace ExpanderDecomposition

open scoped BigOperators

variable {G : Type} [Group G] {S : SoficApproximation G} {T : Finset G}
variable (D : ExpanderDecomposition S T)

/-- The disjoint union of two selected completed components. -/
abbrev componentPairModel
    (L R : ∀ n, D.componentIndex n) (n : ℕ) : FiniteModel :=
  sumModel
    (indexedBlockModel (D.blocks n) (L n))
    (indexedBlockModel (D.blocks n) (R n))

/-- The completed label acting independently on the two selected
components. -/
noncomputable def componentPairMap
    (L R : ∀ n, D.componentIndex n) (n : ℕ) (g : G) :
    Equiv.Perm (D.componentPairModel L R n) :=
  FinitePartialBijection.sumAction
    (D.componentCompletedAction n (L n))
    (D.componentCompletedAction n (R n)) g

@[simp] theorem componentPairMap_inl
    (L R : ∀ n, D.componentIndex n) (n : ℕ) (g : G)
    (x : indexedBlockModel (D.blocks n) (L n)) :
    D.componentPairMap L R n g (Sum.inl x) =
      Sum.inl (D.componentCompletedAction n (L n) g x) := rfl

@[simp] theorem componentPairMap_inr
    (L R : ∀ n, D.componentIndex n) (n : ℕ) (g : G)
    (x : indexedBlockModel (D.blocks n) (R n)) :
    D.componentPairMap L R n g (Sum.inr x) =
      Sum.inr (D.componentCompletedAction n (R n) g x) := rfl

/-- Product failures of the sum action are exactly the disjoint union of the
two local component product-error sets. -/
theorem card_componentPairMap_multiplicationError
    (L R : ∀ n, D.componentIndex n) (n : ℕ) (g h : G) :
    (hammingDisagreement
      (D.componentPairMap L R n (g * h))
      (D.componentPairMap L R n g * D.componentPairMap L R n h)).card =
      (D.componentMultiplicationError n (L n) g h).card +
        (D.componentMultiplicationError n (R n) g h).card := by
  classical
  unfold hammingDisagreement componentMultiplicationError
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ x :
      indexedBlockModel (D.blocks n) (L n) ⊕
        indexedBlockModel (D.blocks n) (R n),
      if D.componentPairMap L R n (g * h) x ≠
        (D.componentPairMap L R n g * D.componentPairMap L R n h) x
      then 1 else 0) = _
  rw [Fintype.sum_sum_type]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  congr 1 <;>
    apply Finset.sum_congr rfl <;>
    intro x _ <;>
    simp only [componentPairMap_inl, componentPairMap_inr,
      Equiv.Perm.mul_apply, Sum.inl.injEq, Sum.inr.injEq]

/-- The selected pair model has the sum of the two component cardinalities. -/
theorem card_componentPairModel
    (L R : ∀ n, D.componentIndex n) (n : ℕ) :
    Fintype.card (D.componentPairModel L R n) =
      (L n).block.card + (R n).block.card := by
  simp [componentPairModel, indexedBlockModel]

/-- Build the multiplicative approximation carried by a selected component
pair.  Both assumptions are concrete asymptotic facts about component sizes
and the local error finsets; no faithfulness premise is present or needed. -/
noncomputable def componentPairMultiplicativeApproximation
    (L R : ∀ n, D.componentIndex n)
    (hcard : ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      M ≤ (L n).block.card + (R n).block.card)
    (hmul : ∀ (g h : G) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      (((D.componentMultiplicationError n (L n) g h).card : ℝ) +
          (D.componentMultiplicationError n (R n) g h).card) /
        ((L n).block.card + (R n).block.card) < ε) :
    MultiplicativeApproximation G where
  model := D.componentPairModel L R
  map := D.componentPairMap L R
  card_tendsToInfinity M := by
    obtain ⟨N, hN⟩ := hcard M
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [D.card_componentPairModel L R n]
    exact hN n hn
  asymptoticallyMultiplicative g h ε hε := by
    obtain ⟨N, hN⟩ := hmul g h ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [hammingDistance, D.card_componentPairMap_multiplicationError L R n g h,
      D.card_componentPairModel L R n]
    push_cast
    exact hN n hn

end ExpanderDecomposition
end NonsoficGroupsExist
