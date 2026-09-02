import GroupApproximation.GGT.VanKampen.Estimating.Incidence

/-!
# The exterior merge needs only that the union is a candidate

`Embedded.ExteriorMergeAvailable` asks, for two distinct exterior regions at a
cell, for a merged candidate carrying an `Embedded.MergeSurgery` and absorbing
their weights.  Reading `MergeSurgery` shows the merged carrier is not a free
choice: its field `mergedFace_mem` says `face ∈ merged.1 ↔ face ∈ first.1 ∨
face ∈ second.1`, so the carrier is forced to be `candidateFaceUnion`.

Taking it to be exactly that union collapses the rest.  `GCellReplacement` then
has the same old and new carrier, so one boundary record serves for both and
`boundaryWord_eq` is `rfl`.  What is left is that the union is a candidate at
all, plus the weight inequality.  `mergeSurgery_of_union` is that reduction.

**The two O52 fields cost nothing here.**  Exterior regions have
`target = none`, and both `Contiguity.target_ne_source` and
`Contiguity.o52Certificate` are stated as `∀ i, target = some i → …`, so a
contiguity for the merged exterior region discharges both by `nofun`.  The
`pasting` field is the one that is not free: the union's boundary cycle needs
its own shelling.
-/

set_option linter.unusedVariables false

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Embedded

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}
  {D : GGT.RelGenSet G Lambda}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

/-- **The merge surgery is free once the union is a candidate.**  Taking the
merged carrier to be the union of the two carriers makes the replacement's old
and new face sets equal, so a single boundary record serves for both and the
boundary words agree by reflexivity. -/
noncomputable def mergeSurgery_of_union
    (first second : Candidate D eps Delta)
    (hcand : IsCandidate D eps Delta (candidateFaceUnion first second))
    (boundary : FaceSetBoundary Delta (candidateFaceUnion first second)) :
    MergeSurgery first second ⟨candidateFaceUnion first second, hcand⟩ where
  replacement :=
    { oldBoundary := boundary
      newBoundary := boundary
      boundaryWord_eq := rfl }
  mergedFace_mem := by
    classical
    intro face
    simp [candidateFaceUnion]

/-- **The exterior merge from a union candidate and its weight.**  This is the
whole remaining content of `ExteriorMergeAvailable`: for every pair of distinct
exterior regions at a cell, the union of their carriers is a candidate whose
weight absorbs both. -/
theorem exteriorMergeAvailable_of_unionCandidates
    (selected : Finset (Candidate D eps Delta))
    (hunion : ∀ (i : Fin Delta.rCellCount)
      (first second : ExteriorRegion selected i), first ≠ second →
      ∃ hcand : IsCandidate D eps Delta
          (candidateFaceUnion first.1 second.1),
        Nonempty (FaceSetBoundary Delta
          (candidateFaceUnion first.1 second.1)) ∧
          first.1.weight + second.1.weight ≤
            (⟨candidateFaceUnion first.1 second.1, hcand⟩ :
              Candidate D eps Delta).weight) :
    ExteriorMergeAvailable selected := by
  intro i first second hne
  obtain ⟨hcand, ⟨boundary⟩, hweight⟩ := hunion i first second hne
  exact ⟨⟨candidateFaceUnion first.1 second.1, hcand⟩,
    ⟨mergeSurgery_of_union first.1 second.1 hcand boundary⟩, hweight⟩

end Embedded
end VanKampen
end GGT
end GroupApproximation
