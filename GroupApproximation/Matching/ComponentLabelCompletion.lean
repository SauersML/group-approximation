import GroupApproximation.Matching.ComponentPinning
import GroupApproximation.Matching.ComponentDivergence
import GroupApproximation.Matching.CompletionGraphEditing
import GroupApproximation.Matching.EdgeWitnessRestriction
import GroupApproximation.Matching.EditedGeneratorExpansion

/-!
# Completed generator labels on one expander component

Restrict every model permutation to a component and complete the resulting
partial permutation on that component.  The completed generator graph differs
from the edited component graph only through generator exits and the local
part of the decomposition's explicit edit witness.
-/

namespace GroupApproximation
namespace ExpanderDecomposition

open scoped BigOperators

variable {G : Type} [Group G] {S : SoficApproximation G} {T : Finset G}
variable (D : ExpanderDecomposition S T)

/-- The ambient model action, completed on one indexed component. -/
noncomputable def componentCompletedAction (n : ℕ) (C : D.componentIndex n)
    (g : G) : Equiv.Perm (indexedBlockModel (D.blocks n) C) :=
  Classical.choose
    (Localization.exists_completion C.block (S.map n g))

/-- Completion agrees with the ambient permutation whenever the image stays
in the component. -/
theorem componentCompletedAction_agrees (n : ℕ) (C : D.componentIndex n)
    (g : G) (x : indexedBlockModel (D.blocks n) C)
    (hx : S.map n g (x : S.model n) ∈ C.block) :
    (D.componentCompletedAction n C g x : S.model n) =
      S.map n g (x : S.model n) := by
  exact Classical.choose_spec
    (Localization.exists_completion C.block (S.map n g)) x hx

/-- The edited graph induced directly on an indexed component. -/
noncomputable abbrev directIndexedComponentGraph
    (n : ℕ) (C : D.componentIndex n) : FiniteMultiGraph :=
  (D.modelGraph n).induce C.block

theorem directIndexedComponentGraph_expands
    (n : ℕ) (C : D.componentIndex n) :
    (D.directIndexedComponentGraph n C).HasCheegerLowerBound D.cheeger := by
  have h := D.component_expands n (D.componentRepresentative n C)
  simpa only [directIndexedComponentGraph, D.componentRepresentative_block n C]
    using h

/-- The actual ambient generator graph induced on one component. -/
noncomputable abbrev actualInducedComponentGraph
    (n : ℕ) (C : D.componentIndex n) : FiniteMultiGraph :=
  (generatorGraph (S.model n) T (S.map n)).induce C.block

/-- Restriction of the decomposition's occurrence edit witness to one
component. -/
noncomputable def componentEditWitness (n : ℕ) (C : D.componentIndex n) :
    EdgeEditWitness (D.actualInducedComponentGraph n C)
      (D.directIndexedComponentGraph n C)
      (Equiv.refl _) := by
  let W := (D.editWitness n).induce C.block C.block (fun _ ↦ Iff.rfl)
  exact
    { sourceKept := W.sourceKept
      targetKept := W.targetKept
      edgeEquiv := W.edgeEquiv
      preservesEndpoints := by
        intro a
        have hvertex :
            EdgeEditWitness.inducedVertexEquiv
              (X := generatorGraph (S.model n) T (S.map n))
              (Z := D.modelGraph n)
              (e := Equiv.refl (S.model n)) C.block C.block
                (fun _ ↦ Iff.rfl) =
              Equiv.refl (D.actualInducedComponentGraph n C).vertex := by
          apply Equiv.ext
          intro x
          rfl
        rw [← hvertex]
        exact W.preservesEndpoints a }

/-- The finite local error budget: four occurrences per generator exit and
two occurrences per locally unmatched edit-witness edge. -/
noncomputable def componentLabelEditBudget
    (n : ℕ) (C : D.componentIndex n) : ℕ :=
  4 * ∑ t : T,
      (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
        S.map n t.1 (x : S.model n) ∉ C.block).card +
    2 * (D.componentEditWitness n C).unmatchedCount

/-- The completed component generator graph is within the explicit local
budget of the edited expanding component graph. -/
theorem componentCompletedGraph_editDistance_le
    (n : ℕ) (C : D.componentIndex n) :
    (generatorGraph (indexedBlockModel (D.blocks n) C) T
      (D.componentCompletedAction n C)).editDistance
        (D.directIndexedComponentGraph n C) (Equiv.refl _) ≤
      D.componentLabelEditBudget n C := by
  let X := generatorGraph (indexedBlockModel (D.blocks n) C) T
    (D.componentCompletedAction n C)
  let Y := D.actualInducedComponentGraph n C
  let Z := D.directIndexedComponentGraph n C
  have hcompletion : X.editDistance Y (Equiv.refl _) ≤
      4 * ∑ t : T,
        (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n t.1 (x : S.model n) ∉ C.block).card := by
    refine (CompletionGraphEditing.editDistance_le C.block T (S.map n)
      (D.componentCompletedAction n C)).trans ?_
    apply Nat.mul_le_mul_left
    apply Finset.sum_le_sum
    intro t _
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    intro hin
    exact hx (D.componentCompletedAction_agrees n C t.1 x hin)
  have hwitness : Y.editDistance Z (Equiv.refl _) ≤
      2 * (D.componentEditWitness n C).unmatchedCount := by
    exact (D.componentEditWitness n C).editDistance_le_two_mul_unmatchedCount
  have htriangle := FiniteMultiGraph.editDistance_triangle
    X Y Z (Equiv.refl _) (Equiv.refl _)
  change X.editDistance Z (Equiv.refl _) ≤ _
  exact htriangle.trans (Nat.add_le_add hcompletion hwitness)

/-- Whenever the local edit budget is below half the Cheeger mass at scale
`m`, the completed component labels have the tagged expansion required by
the partial-intertwiner separation theorem. -/
theorem componentCompletedAction_taggedExpansion
    (n : ℕ) (C : D.componentIndex n) (m : ℕ)
    (hsmall : (D.componentLabelEditBudget n C : ℝ) < D.cheeger * m / 2) :
    FinitePartialBijection.HasTaggedExpansionAtScale
      (fun t : T ↦ D.componentCompletedAction n C t.1)
      (D.cheeger / 4) m := by
  apply hasTaggedExpansionAtScale_of_editDistance T
    (D.componentCompletedAction n C) (D.directIndexedComponentGraph n C)
    (Equiv.refl _) (D.directIndexedComponentGraph_expands n C)
  have hle :
      (((generatorGraph (indexedBlockModel (D.blocks n) C) T
        (D.componentCompletedAction n C)).editDistance
          (D.directIndexedComponentGraph n C) (Equiv.refl _) : ℕ) : ℝ) ≤
        D.componentLabelEditBudget n C := by
    exact_mod_cast D.componentCompletedGraph_editDistance_le n C
  exact hle.trans_lt hsmall

/-- Generator exits, summed over the distinct components, are exactly the
global almost-invariance error of the component partition. -/
theorem sum_componentGeneratorExits (n : ℕ) (t : G) :
    (∑ C : D.componentIndex n,
      ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
        S.map n t (x : S.model n) ∉ C.block).card : ℝ)) =
      ((Finset.univ.filter fun x : S.model n ↦
        (D.blocks n).block (S.map n t x) ≠
          (D.blocks n).block x).card : ℝ) := by
  classical
  rw [← BlockIndex.sum_card_filter (D.blocks n) (fun x ↦
    (D.blocks n).block (S.map n t x) ≠ (D.blocks n).block x)]
  apply Finset.sum_congr rfl
  intro C _
  norm_cast
  have hsets :
      (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
        S.map n t (x : S.model n) ∉ C.block) =
      (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
        (D.blocks n).block (S.map n t (x : S.model n)) ≠
          (D.blocks n).block (x : S.model n)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hout heq
      apply hout
      have hxmem : (x : S.model n) ∈
          (D.blocks n).block (BlockIndex.representative (D.blocks n) C) := by
        rw [BlockIndex.block_representative]
        exact x.2
      have hxblock : (D.blocks n).block (x : S.model n) = C.block :=
        ((D.blocks n).eq_of_mem
          (BlockIndex.representative (D.blocks n) C) _ hxmem).trans
            (BlockIndex.block_representative (D.blocks n) C)
      have himageself : S.map n t (x : S.model n) ∈
          (D.blocks n).block (S.map n t (x : S.model n)) :=
        (D.blocks n).self_mem _
      rw [heq, hxblock] at himageself
      exact himageself
    · intro hneq hin
      apply hneq
      have hxmem : (x : S.model n) ∈
          (D.blocks n).block (BlockIndex.representative (D.blocks n) C) := by
        rw [BlockIndex.block_representative]
        exact x.2
      have hxblock : (D.blocks n).block (x : S.model n) = C.block :=
        ((D.blocks n).eq_of_mem
          (BlockIndex.representative (D.blocks n) C) _ hxmem).trans
            (BlockIndex.block_representative (D.blocks n) C)
      have himagemem : S.map n t (x : S.model n) ∈
          (D.blocks n).block (BlockIndex.representative (D.blocks n) C) := by
        rw [BlockIndex.block_representative]
        exact hin
      have himage : (D.blocks n).block (S.map n t (x : S.model n)) = C.block :=
        ((D.blocks n).eq_of_mem
          (BlockIndex.representative (D.blocks n) C) _ himagemem).trans
            (BlockIndex.block_representative (D.blocks n) C)
      exact himage.trans hxblock.symm
  rw [hsets]

/-- On one component, the chosen completion can disagree with the ambient
permutation only where the ambient image leaves that component. -/
theorem componentCompletedAction_disagreement_le_exit
    (n : ℕ) (C : D.componentIndex n) (g : G) :
    (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
      (D.componentCompletedAction n C g x : S.model n) ≠
        S.map n g (x : S.model n)).card ≤
      (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
        S.map n g (x : S.model n) ∉ C.block).card := by
  classical
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  intro hin
  exact hx (D.componentCompletedAction_agrees n C g x hin)

/-- Summed over all components, completion disagreement is bounded by the
global block-crossing error of the ambient permutation. -/
theorem sum_componentCompletedAction_disagreement_le
    (n : ℕ) (g : G) :
    (∑ C : D.componentIndex n,
      ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
        (D.componentCompletedAction n C g x : S.model n) ≠
          S.map n g (x : S.model n)).card : ℝ)) ≤
      ((Finset.univ.filter fun x : S.model n ↦
        (D.blocks n).block (S.map n g x) ≠
          (D.blocks n).block x).card : ℝ) := by
  calc
    _ ≤ ∑ C : D.componentIndex n,
        ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          S.map n g (x : S.model n) ∉ C.block).card : ℝ) := by
      apply Finset.sum_le_sum
      intro C _
      exact_mod_cast D.componentCompletedAction_disagreement_le_exit n C g
    _ = _ := D.sum_componentGeneratorExits n g

/-- For every fixed group element, the total number of component points on
which the chosen completions differ from the ambient sofic model is
negligible.  This is the quantitative bridge from the global approximation
to the componentwise completed labels. -/
theorem componentCompletedAction_disagreement_sum_negligible
    (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set G) = ⊤) (g : G) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ∑ C : D.componentIndex n,
        ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
          (D.componentCompletedAction n C g x : S.model n) ≠
            S.map n g (x : S.model n)).card : ℝ)) := by
  apply Negligible.mono_nonneg (fun n ↦ by
      exact_mod_cast Nat.zero_le (Fintype.card (S.model n)))
    (fun _ ↦ by positivity)
    (fun n ↦ D.sum_componentCompletedAction_disagreement_le n g)
  have hall := D.all_almost_invariant hsymm hgen g
  change Negligible S.cardScale.value
    (fun n ↦ ((wordCrossing (D.blocks n) (S.map n g)).card : ℝ)) at hall
  change Negligible S.cardScale.value (fun n ↦
    ((Finset.univ.filter fun x : S.model n ↦
      (D.blocks n).block (S.map n g x) ≠
        (D.blocks n).block x).card : ℝ))
  simpa only [wordCrossing] using hall

/-- Restricting the occurrence edit witness to every component counts each
globally unmatched occurrence at most once. -/
theorem sum_componentEditWitness_unmatchedCount_le (n : ℕ) :
    ∑ C : D.componentIndex n,
      (D.componentEditWitness n C).unmatchedCount ≤
        (D.editWitness n).unmatchedCount := by
  classical
  let W := D.editWitness n
  have hlocal (C : D.componentIndex n) :
      (D.componentEditWitness n C).unmatchedCount ≤
        (W.sourceUnmatched.filter fun e ↦
          (generatorGraph (S.model n) T (S.map n)).first e ∈ C.block).card +
        (W.targetUnmatched.filter fun e ↦
          (D.modelGraph n).first e ∈ C.block).card := by
    have h := W.induce_unmatchedCount_le_filters C.block C.block
      (fun _ ↦ Iff.rfl)
    change (W.induce C.block C.block (fun _ ↦ Iff.rfl)).unmatchedCount ≤ _
    simpa only [modelGraph] using h
  have hsum := (Finset.univ : Finset (D.componentIndex n)).sum_le_sum
    fun C _ ↦ hlocal C
  rw [Finset.sum_add_distrib] at hsum
  have hsource := BlockIndex.sum_card_filter_mem_block (D.blocks n)
    W.sourceUnmatched
    (fun e ↦ (generatorGraph (S.model n) T (S.map n)).first e)
  have htarget := BlockIndex.sum_card_filter_mem_block (D.blocks n)
    W.targetUnmatched (fun e ↦ (D.modelGraph n).first e)
  change ∑ C : D.componentIndex n,
      (D.componentEditWitness n C).unmatchedCount ≤
    W.sourceUnmatched.card + W.targetUnmatched.card
  exact hsum.trans (Nat.add_le_add hsource htarget)

/-- The sum of all local completed-label edit budgets has negligible density
in the ambient finite models. -/
theorem componentLabelEditBudget_sum_negligible :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ∑ C : D.componentIndex n,
        (D.componentLabelEditBudget n C : ℝ)) := by
  have hexitEach (t : T) := D.almost_invariant t.1 t.2
  have hexits : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ∑ t : T,
        ((Finset.univ.filter fun x : S.model n ↦
          (D.blocks n).block (S.map n t.1 x) ≠
            (D.blocks n).block x).card : ℝ)) :=
    Negligible.sum (Finset.univ : Finset T) _
      (fun t _ ↦ hexitEach t)
  have hmajor := Negligible.add (Negligible.const_mul 4 hexits)
    (Negligible.const_mul 2 D.unmatched_negligible)
  refine Negligible.mono_nonneg (fun _ ↦ by positivity) (fun _ ↦ by positivity)
    (fun n ↦ ?_) hmajor
  have hw := D.sum_componentEditWitness_unmatchedCount_le n
  unfold componentLabelEditBudget
  push_cast
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  calc
    4 * ∑ C : D.componentIndex n,
          ∑ t : T,
            ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) C ↦
              S.map n t.1 (x : S.model n) ∉ C.block).card : ℝ) +
        2 * ∑ C : D.componentIndex n,
          ((D.componentEditWitness n C).unmatchedCount : ℝ) =
      4 * ∑ t : T,
          ((Finset.univ.filter fun x : S.model n ↦
            (D.blocks n).block (S.map n t.1 x) ≠
              (D.blocks n).block x).card : ℝ) +
        2 * ∑ C : D.componentIndex n,
          ((D.componentEditWitness n C).unmatchedCount : ℝ) := by
      congr 1
      congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun (t : T) _ ↦
        D.sum_componentGeneratorExits n t.1
    _ ≤ 4 * ∑ t : T,
          ((Finset.univ.filter fun x : S.model n ↦
            (D.blocks n).block (S.map n t.1 x) ≠
              (D.blocks n).block x).card : ℝ) +
        2 * ((D.editWitness n).unmatchedCount : ℝ) := by
      gcongr
      exact_mod_cast hw

end ExpanderDecomposition
end GroupApproximation
