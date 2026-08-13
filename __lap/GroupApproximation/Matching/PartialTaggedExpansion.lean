import GroupApproximation.Matching.PartialEquivarianceBoundary
import GroupApproximation.Sofic.AlmostAutomorphism

/-!
# From permutation-label expansion to tagged expansion

The existing directed-expansion API stores labels as a finite set of
permutations.  Partial intertwiners retain the label tag.  Passing to the
subtype of a label finset changes no boundary cardinality, so the existing
expansion theorem supplies the tagged form verbatim.
-/

namespace GroupApproximation

variable {Y : FiniteModel}

/-- A finite permutation label set, regarded as a finite label type. -/
abbrev PermutationLabel (S : Finset (Equiv.Perm Y)) := ↑S

/-- Evaluation action of a tagged permutation label. -/
def permutationLabelAction (S : Finset (Equiv.Perm Y)) :
    PermutationLabel S → Equiv.Perm Y := fun s ↦ s.1

/-- Forgetting the subtype tag identifies tagged boundary occurrences with
the directed boundary occurrences used by `AlmostAutomorphism`. -/
theorem card_taggedBoundary_permutationLabelAction
    (S : Finset (Equiv.Perm Y)) (A : Finset Y) :
    (FinitePartialBijection.taggedBoundary
      (permutationLabelAction S) A).card =
      (AlmostAutomorphism.directedBoundary Y S A).card := by
  classical
  apply Finset.card_bij (fun p _ ↦ ((p.1.1 : Equiv.Perm Y), p.2))
  · intro p hp
    rw [FinitePartialBijection.mem_taggedBoundary] at hp
    rw [AlmostAutomorphism.mem_directedBoundary]
    exact ⟨p.1.2, hp⟩
  · intro p _ q _ hpq
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun r : Equiv.Perm Y × Y ↦ r.1) hpq
    · exact congrArg (fun r : Equiv.Perm Y × Y ↦ r.2) hpq
  · intro p hp
    rw [AlmostAutomorphism.mem_directedBoundary] at hp
    refine ⟨(⟨p.1, hp.1⟩, p.2), ?_, rfl⟩
    rw [FinitePartialBijection.mem_taggedBoundary]
    exact hp.2

/-- Existing directed expansion implies the tagged expansion needed for
partial intertwiners. -/
theorem hasTaggedExpansionAtScale_of_hasDirectedExpansionAtScale
    (S : Finset (Equiv.Perm Y)) {h : ℝ} {m : ℕ}
    (hexp : AlmostAutomorphism.HasDirectedExpansionAtScale Y S h m) :
    FinitePartialBijection.HasTaggedExpansionAtScale
      (permutationLabelAction S) h m := by
  refine ⟨hexp.1, fun A hm hhalf ↦ ?_⟩
  rw [card_taggedBoundary_permutationLabelAction]
  exact hexp.2 A hm hhalf

end GroupApproximation
