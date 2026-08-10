import NonsoficGroupsExist.Matching.ComponentPinning
import NonsoficGroupsExist.Matching.CompletionGraphEditing
import NonsoficGroupsExist.Matching.EdgeWitnessRestriction
import NonsoficGroupsExist.Matching.EditedGeneratorExpansion

/-!
# Completed generator labels on one expander component

Restrict every model permutation to a component and complete the resulting
partial permutation on that component.  The completed generator graph differs
from the edited component graph only through generator exits and the local
part of the decomposition's explicit edit witness.
-/

namespace NonsoficGroupsExist
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
        simpa only [W, EdgeEditWitness.inducedVertexEquiv,
          Equiv.refl_apply] using W.preservesEndpoints a }

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
set_option maxHeartbeats 800000 in
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
    exact CompletionGraphEditing.canonicalCompletion_editDistance_le
      C.block T (S.map n)
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
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hout heq
    apply hout
    have hself : (x : S.model n) ∈
        (D.blocks n).block (x : S.model n) := (D.blocks n).self_mem _
    have hxblock : (D.blocks n).block (x : S.model n) = C.block :=
      (D.blocks n).eq_of_mem _ _ x.2
    rw [heq, hxblock]
    exact hself
  · intro hneq hin
    apply hneq
    have hxblock : (D.blocks n).block (x : S.model n) = C.block :=
      (D.blocks n).eq_of_mem _ _ x.2
    have himage : (D.blocks n).block (S.map n t (x : S.model n)) = C.block :=
      (D.blocks n).eq_of_mem _ _ hin
    exact himage.trans hxblock.symm

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
    simpa only [componentEditWitness, W, actualInducedComponentGraph,
      directIndexedComponentGraph] using h
  have hsum := Finset.sum_le_sum fun C _ ↦ hlocal C
  rw [Finset.sum_add_distrib] at hsum
  have hsource := BlockIndex.sum_card_filter_mem_block (D.blocks n)
    W.sourceUnmatched
    (fun e ↦ (generatorGraph (S.model n) T (S.map n)).first e)
  have htarget := BlockIndex.sum_card_filter_mem_block (D.blocks n)
    W.targetUnmatched (fun e ↦ (D.modelGraph n).first e)
  unfold EdgeEditWitness.unmatchedCount
  omega

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
  refine Negligible.mono (fun _ ↦ by positivity) (fun _ ↦ by positivity)
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
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      exact D.sum_componentGeneratorExits n t.1
    _ ≤ 4 * ∑ t : T,
          ((Finset.univ.filter fun x : S.model n ↦
            (D.blocks n).block (S.map n t.1 x) ≠
              (D.blocks n).block x).card : ℝ) +
        2 * ((D.editWitness n).unmatchedCount : ℝ) := by
      gcongr
      exact_mod_cast hw

end ExpanderDecomposition
end NonsoficGroupsExist
