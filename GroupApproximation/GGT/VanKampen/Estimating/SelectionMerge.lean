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

open GroupApproximation.WordMetric

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}
  {D : GGT.RelGenSet G Lambda}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {faces : Finset Delta.toCombMap.Face}

/-! ## Building the merged exterior region -/

/-- **A boundary-target contiguity from its geometry alone.**  When the target
is the outer boundary both `O52` fields are vacuous, so a producer of a merged
exterior region supplies only geometry: the region's boundary record and its
shelling, the source and outer arcs, the two short sides, and the boundary
decomposition.  `targetBoundaryDarts` at a `none` target is the arc's own
darts, so the decomposition is stated in that form.

This is what Osin's 2-gon step asks a producer to build: "one can include the
`e`-contiguity subdiagrams corresponding to the edges `e` and `f` into a single
`e`-contiguity subdiagram in the obvious way". -/
def boundaryContiguity
    (boundary : FaceSetBoundary Delta faces)
    (source : Fin Delta.rCellCount)
    (sourceArc : CyclicArc (cellDarts Delta source))
    (outerArc :
      CyclicArc (targetDarts Delta (none : Option (Fin Delta.rCellCount))))
    (rightSide leftSide : List Delta.toCombMap.Dart)
    (hdecomposition : boundary.cycle =
      sourceArc.reverseDarts ++ rightSide ++ outerArc.darts ++ leftSide)
    (hrightLength : rightSide.length ≤ eps)
    (hleftLength : leftSide.length ≤ eps)
    (hrightNorm : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal (dartWord Delta rightSide)) ≤ eps)
    (hleftNorm : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal (dartWord Delta leftSide)) ≤ eps)
    (shelling : ∃ l : List Delta.toCombMap.Face,
      FaceShelling Delta faces l boundary.cycle) :
    Contiguity D eps Delta faces where
  boundary := boundary
  source := source
  target := none
  sourceArc := sourceArc
  targetArc := outerArc
  rightSide := rightSide
  leftSide := leftSide
  boundary_decomposition := hdecomposition
  rightSide_length_le := hrightLength
  leftSide_length_le := hleftLength
  rightSide_norm_le := hrightNorm
  leftSide_norm_le := hleftNorm
  target_ne_source := by
    intro i h
    simp at h
  o52Certificate := by
    intro i h
    simp at h
  pasting := shelling

/-- The union of two carriers is a candidate as soon as the merged exterior
region's geometry is supplied.  With `mergeSurgery_of_union` and
`exteriorMergeAvailable_of_unionCandidates` this is the whole route to
`ExteriorMergeAvailable`. -/
theorem isCandidate_of_boundaryContiguity
    (boundary : FaceSetBoundary Delta faces)
    (source : Fin Delta.rCellCount)
    (sourceArc : CyclicArc (cellDarts Delta source))
    (outerArc :
      CyclicArc (targetDarts Delta (none : Option (Fin Delta.rCellCount))))
    (rightSide leftSide : List Delta.toCombMap.Dart)
    (hdecomposition : boundary.cycle =
      sourceArc.reverseDarts ++ rightSide ++ outerArc.darts ++ leftSide)
    (hrightLength : rightSide.length ≤ eps)
    (hleftLength : leftSide.length ≤ eps)
    (hrightNorm : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal (dartWord Delta rightSide)) ≤ eps)
    (hleftNorm : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal (dartWord Delta leftSide)) ≤ eps)
    (shelling : ∃ l : List Delta.toCombMap.Face,
      FaceShelling Delta faces l boundary.cycle) :
    IsCandidate D eps Delta faces :=
  ⟨boundaryContiguity boundary source sourceArc outerArc rightSide leftSide
    hdecomposition hrightLength hleftLength hrightNorm hleftNorm shelling⟩

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
            Candidate.weight
              (⟨candidateFaceUnion first.1 second.1, hcand⟩ :
                Candidate D eps Delta)) :
    ExteriorMergeAvailable selected := by
  intro i first second hne
  obtain ⟨hcand, ⟨boundary⟩, hweight⟩ := hunion i first second hne
  exact ⟨⟨candidateFaceUnion first.1 second.1, hcand⟩,
    ⟨mergeSurgery_of_union first.1 second.1 hcand boundary⟩, hweight⟩

end Embedded
end VanKampen
end GGT
end GroupApproximation
