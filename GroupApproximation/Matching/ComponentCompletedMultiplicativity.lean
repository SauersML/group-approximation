import GroupApproximation.Matching.ComponentLabelCompletion
import GroupApproximation.Sofic.SoficErrors

/-!
# Multiplicativity of completed component labels

The arbitrary permutation completion on each expander component inherits the
ambient sofic multiplication law after summing over all components.  Every
local product failure is charged to one ambient multiplication failure or to
one of the three completion-disagreement sets for `g`, `h`, and `g * h`.
-/

namespace GroupApproximation
namespace ExpanderDecomposition

open scoped BigOperators

variable {G : Type} [Group G] {S : SoficApproximation G} {T : Finset G}
variable (D : ExpanderDecomposition S T)

/-- Points of a component where its chosen completion differs from the
ambient permutation. -/
noncomputable def componentCompletionDisagreement
    (n : ℕ) (C : D.componentIndex n) (g : G) :
    Finset (indexedBlockModel (D.blocks n) C) := by
  classical
  exact Finset.univ.filter fun x ↦
    (D.componentCompletedAction n C g x : S.model n) ≠
      S.map n g (x : S.model n)

/-- Failures of the product law inside one completed component action. -/
noncomputable def componentMultiplicationError
    (n : ℕ) (C : D.componentIndex n) (g h : G) :
    Finset (indexedBlockModel (D.blocks n) C) := by
  classical
  exact Finset.univ.filter fun x ↦
    D.componentCompletedAction n C (g * h) x ≠
      (D.componentCompletedAction n C g *
        D.componentCompletedAction n C h) x

/-- Points where the completed label assigned to the group identity moves a
component vertex. -/
noncomputable def componentIdentityError
    (n : ℕ) (C : D.componentIndex n) :
    Finset (indexedBlockModel (D.blocks n) C) := by
  classical
  exact Finset.univ.filter fun x ↦
    D.componentCompletedAction n C (1 : G) x ≠ x

/-- Ambient multiplication failures, restricted only by the source
component. -/
noncomputable def componentAmbientMultiplicationError
    (n : ℕ) (C : D.componentIndex n) (g h : G) :
    Finset (indexedBlockModel (D.blocks n) C) := by
  classical
  exact Finset.univ.filter fun x ↦
    S.map n (g * h) (x : S.model n) ≠
      S.map n g (S.map n h (x : S.model n))

/-- The disagreement set for `g`, pulled back through the completed
permutation for `h`. -/
noncomputable def transportedComponentCompletionDisagreement
    (n : ℕ) (C : D.componentIndex n) (g h : G) :
    Finset (indexedBlockModel (D.blocks n) C) := by
  classical
  exact Finset.univ.filter fun x ↦
    (D.componentCompletedAction n C g
        (D.componentCompletedAction n C h x) : S.model n) ≠
      S.map n g
        (D.componentCompletedAction n C h x : S.model n)

/-- Pulling a completion-disagreement set back through a component
permutation preserves its cardinality. -/
theorem card_transportedComponentCompletionDisagreement
    (n : ℕ) (C : D.componentIndex n) (g h : G) :
    (D.transportedComponentCompletionDisagreement n C g h).card =
      (D.componentCompletionDisagreement n C g).card := by
  classical
  let q := D.componentCompletedAction n C h
  apply Finset.card_bij (fun x _ ↦ q x)
  · intro x hx
    simp only [transportedComponentCompletionDisagreement,
      componentCompletionDisagreement, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx ⊢
    exact hx
  · intro x _ y _ hxy
    exact q.injective hxy
  · intro y hy
    refine ⟨q⁻¹ y, ?_, q.apply_symm_apply y⟩
    simp only [transportedComponentCompletionDisagreement,
      componentCompletionDisagreement, Finset.mem_filter, Finset.mem_univ,
      true_and] at hy ⊢
    change (D.componentCompletedAction n C g (q (q⁻¹ y)) : S.model n) ≠
      S.map n g (q (q⁻¹ y) : indexedBlockModel (D.blocks n) C)
    simpa [q] using hy

/-- A local completed product failure is charged to the ambient product law
or to completion disagreement for one of the three involved elements. -/
theorem componentMultiplicationError_card_le
    (n : ℕ) (C : D.componentIndex n) (g h : G) :
    (D.componentMultiplicationError n C g h).card ≤
      (D.componentCompletionDisagreement n C (g * h)).card +
      (D.componentAmbientMultiplicationError n C g h).card +
      (D.componentCompletionDisagreement n C h).card +
      (D.componentCompletionDisagreement n C g).card := by
  classical
  let A := D.componentCompletionDisagreement n C (g * h)
  let B := D.componentAmbientMultiplicationError n C g h
  let E := D.componentCompletionDisagreement n C h
  let F := D.transportedComponentCompletionDisagreement n C g h
  have hAB := Finset.card_union_le A B
  have hABE := Finset.card_union_le (A ∪ B) E
  have hsubset : D.componentMultiplicationError n C g h ⊆
      ((A ∪ B) ∪ E) ∪ F := by
    intro x hx
    by_cases hA : x ∈ A
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ hA))
    by_cases hB : x ∈ B
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ hB))
    by_cases hE : x ∈ E
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hE)
    by_cases hF : x ∈ F
    · exact Finset.mem_union_right _ hF
    exfalso
    simp only [componentMultiplicationError, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx
    simp only [A, componentCompletionDisagreement, Finset.mem_filter,
      Finset.mem_univ, true_and, not_not] at hA
    simp only [B, componentAmbientMultiplicationError, Finset.mem_filter,
      Finset.mem_univ, true_and, not_not] at hB
    simp only [E, componentCompletionDisagreement, Finset.mem_filter,
      Finset.mem_univ, true_and, not_not] at hE
    simp only [F, transportedComponentCompletionDisagreement,
      Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hF
    apply hx
    apply Subtype.ext
    change (D.componentCompletedAction n C (g * h) x : S.model n) =
      (D.componentCompletedAction n C g
        (D.componentCompletedAction n C h x) : S.model n)
    calc
      (D.componentCompletedAction n C (g * h) x : S.model n) =
          S.map n (g * h) (x : S.model n) := hA
      _ = S.map n g (S.map n h (x : S.model n)) := hB
      _ = S.map n g
          (D.componentCompletedAction n C h x : S.model n) :=
        congrArg (S.map n g) hE.symm
      _ = (D.componentCompletedAction n C g
          (D.componentCompletedAction n C h x) : S.model n) := hF.symm
  calc
    (D.componentMultiplicationError n C g h).card ≤
        (((A ∪ B) ∪ E) ∪ F).card := Finset.card_le_card hsubset
    _ ≤ ((A ∪ B) ∪ E).card + F.card := Finset.card_union_le _ _
    _ ≤ (A ∪ B).card + E.card + F.card := by
      omega
    _ ≤ (A.card + B.card) + E.card + F.card := by
      omega
    _ = A.card + B.card + E.card +
        (D.componentCompletionDisagreement n C g).card := by
      rw [D.card_transportedComponentCompletionDisagreement n C g h]
    _ = _ := by rfl

/-- Summed over the component partition, completed multiplication failures
are bounded by the ambient multiplication error plus the three total
completion-disagreement errors. -/
theorem sum_componentMultiplicationError_le
    (n : ℕ) (g h : G) :
    (∑ C : D.componentIndex n,
      ((D.componentMultiplicationError n C g h).card : ℝ)) ≤
      ((S.multiplicationError n g h).card : ℝ) +
      ∑ C : D.componentIndex n,
        (((D.componentCompletionDisagreement n C (g * h)).card : ℝ) +
          ((D.componentCompletionDisagreement n C h).card : ℝ) +
          ((D.componentCompletionDisagreement n C g).card : ℝ)) := by
  have hlocal : (∑ C : D.componentIndex n,
      ((D.componentMultiplicationError n C g h).card : ℝ)) ≤
      ∑ C : D.componentIndex n,
        (((D.componentCompletionDisagreement n C (g * h)).card : ℝ) +
          ((D.componentAmbientMultiplicationError n C g h).card : ℝ) +
          ((D.componentCompletionDisagreement n C h).card : ℝ) +
          ((D.componentCompletionDisagreement n C g).card : ℝ)) := by
    apply Finset.sum_le_sum
    intro C _
    exact_mod_cast D.componentMultiplicationError_card_le n C g h
  have hambient : (∑ C : D.componentIndex n,
      ((D.componentAmbientMultiplicationError n C g h).card : ℝ)) =
      ((S.multiplicationError n g h).card : ℝ) := by
    simpa only [componentAmbientMultiplicationError,
      SoficApproximation.multiplicationError] using
      BlockIndex.sum_card_filter (D.blocks n) (fun x : S.model n ↦
        S.map n (g * h) x ≠ S.map n g (S.map n h x))
  calc
    _ ≤ _ := hlocal
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      rw [hambient]
      ring

/-- The completed labels satisfy the group multiplication law outside a
set of negligible total component mass. -/
theorem componentMultiplicationError_sum_negligible
    (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set G) = ⊤) (g h : G) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ∑ C : D.componentIndex n,
        ((D.componentMultiplicationError n C g h).card : ℝ)) := by
  have hgh := D.componentCompletedAction_disagreement_sum_negligible
    hsymm hgen (g * h)
  have hh := D.componentCompletedAction_disagreement_sum_negligible
    hsymm hgen h
  have hg := D.componentCompletedAction_disagreement_sum_negligible
    hsymm hgen g
  have hmajor := Negligible.add (S.multiplicationError_negligible g h)
    (Negligible.add hgh (Negligible.add hh hg))
  have hmajor' : Negligible
      (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ((S.multiplicationError n g h).card : ℝ) +
        (∑ C : D.componentIndex n,
          ((D.componentCompletionDisagreement n C (g * h)).card : ℝ)) +
        ((∑ C : D.componentIndex n,
          ((D.componentCompletionDisagreement n C h).card : ℝ)) +
        ∑ C : D.componentIndex n,
          ((D.componentCompletionDisagreement n C g).card : ℝ))) := by
    apply Negligible.congr hmajor
    intro n
    simp only [componentCompletionDisagreement]
    ring
  apply Negligible.mono_nonneg (fun n ↦ by
      exact_mod_cast Nat.zero_le (Fintype.card (S.model n)))
    (fun _ ↦ by positivity) (fun n ↦ ?_) hmajor'
  calc
    (∑ C : D.componentIndex n,
      ((D.componentMultiplicationError n C g h).card : ℝ)) ≤
        ((S.multiplicationError n g h).card : ℝ) +
        ∑ C : D.componentIndex n,
          (((D.componentCompletionDisagreement n C (g * h)).card : ℝ) +
            ((D.componentCompletionDisagreement n C h).card : ℝ) +
            ((D.componentCompletionDisagreement n C g).card : ℝ)) :=
      D.sum_componentMultiplicationError_le n g h
    _ = ((S.multiplicationError n g h).card : ℝ) +
        (∑ C : D.componentIndex n,
          ((D.componentCompletionDisagreement n C (g * h)).card : ℝ)) +
        ((∑ C : D.componentIndex n,
          ((D.componentCompletionDisagreement n C h).card : ℝ)) +
        ∑ C : D.componentIndex n,
          ((D.componentCompletionDisagreement n C g).card : ℝ)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      ring

/-- A completed identity-label failure is either a completion disagreement
or an ambient identity error. -/
theorem componentIdentityError_card_le
    (n : ℕ) (C : D.componentIndex n) :
    (D.componentIdentityError n C).card ≤
      (D.componentCompletionDisagreement n C (1 : G)).card +
        (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n (1 : G) (x : S.model n) ≠ (x : S.model n)).card := by
  classical
  let A := D.componentCompletionDisagreement n C (1 : G)
  let B := Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
    S.map n (1 : G) (x : S.model n) ≠ (x : S.model n)
  calc
    (D.componentIdentityError n C).card ≤ (A ∪ B).card := by
      apply Finset.card_le_card
      intro x hx
      by_cases hA : x ∈ A
      · exact Finset.mem_union_left _ hA
      apply Finset.mem_union_right
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      intro hambient
      apply hA
      simp only [A, componentCompletionDisagreement, Finset.mem_filter,
        Finset.mem_univ, true_and]
      intro hcompletion
      have hxne : D.componentCompletedAction n C (1 : G) x ≠ x := by
        simpa only [componentIdentityError, Finset.mem_filter,
          Finset.mem_univ, true_and] using hx
      apply hxne
      apply Subtype.ext
      exact hcompletion.trans hambient
    _ ≤ A.card + B.card := Finset.card_union_le _ _
    _ = _ := by rfl

/-- The completed identity label moves only negligible total component
mass. -/
theorem componentIdentityError_sum_negligible
    (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set G) = ⊤) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ∑ C : D.componentIndex n,
        ((D.componentIdentityError n C).card : ℝ)) := by
  have hcompletion :=
    D.componentCompletedAction_disagreement_sum_negligible hsymm hgen (1 : G)
  have hmajor := Negligible.add hcompletion S.identityError_negligible
  apply Negligible.mono_nonneg (fun n ↦ by
      exact_mod_cast Nat.zero_le (Fintype.card (S.model n)))
    (fun _ ↦ by positivity) (fun n ↦ ?_) hmajor
  calc
    (∑ C : D.componentIndex n,
      ((D.componentIdentityError n C).card : ℝ)) ≤
        ∑ C : D.componentIndex n,
          (((D.componentCompletionDisagreement n C (1 : G)).card : ℝ) +
            ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
              S.map n (1 : G) (x : S.model n) ≠
                (x : S.model n)).card : ℝ)) := by
      apply Finset.sum_le_sum
      intro C _
      exact_mod_cast D.componentIdentityError_card_le n C
    _ = (∑ C : D.componentIndex n,
          ((D.componentCompletionDisagreement n C (1 : G)).card : ℝ)) +
        ((S.identityError n).card : ℝ) := by
      rw [Finset.sum_add_distrib]
      congr 1
      simpa only [SoficApproximation.identityError,
        SoficApproximation.movedVertices] using
        BlockIndex.sum_card_filter (D.blocks n) (fun x : S.model n ↦
          S.map n (1 : G) x ≠ x)
    _ = _ := by
      simp only [componentCompletionDisagreement]

end ExpanderDecomposition
end GroupApproximation
