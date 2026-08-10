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

end ExpanderDecomposition
end NonsoficGroupsExist
