import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCopyWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellCopyWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Thickening the edges between two selected regions: the statement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`, where `s_1, s_2` are side arcs of contiguity subdiagrams.

The pocket walk of two regions `x`, `y` uses no edge in both directions only if no edge joins a
face of `x` to a face of `y` (the field `regions` of `PocketWalk.CopyClean`,
`Estimating/OsinPocketCopyWalk.lean`, and of `CellPocketWalk.CopyClean`,
`Estimating/OsinPocketCellCopyWalk.lean`).  On an optimal diagram two selected regions can meet
along an edge of their sides.  Doubling that edge inside the face `f` of one region
(`FaceEdgeDoubling.diagram`) puts a G-cell digon between the two regions.  The digon must lie
in neither region, so the region holding `f` changes: `f` becomes the retained face, and the
side dart `w_j` is replaced by the new dart (`FaceEdgeDoubling.dartImage`).

* `IsRegionPairDart`: a dart of a face with at least two darts, lying in a selected region,
  whose reverse lies in a different selected region.
* `regionPairCount`: the number of region-pair darts, and `regionPairCount_eq_zero_iff`.
* `regions_of_noRegionPairDart`: without region-pair darts, no edge joins a face of `x` to a face
  of `y`.  This is the field `regions`, under the hypothesis that one of the two faces of that
  edge has at least two darts.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.RegionPairThickening

open Embedded
open scoped Classical

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}

/-- A **region-pair dart** of a family of regions: a dart of a face with at least two darts,
lying in a region of the family, whose reverse lies in a different region of the family. -/
def IsRegionPairDart (Delta : DiscDiagram.{u, w, v} W)
    (family : Finset (RegionCandidate D eps Delta)) (x : Delta.toCombMap.Dart) : Prop :=
  1 < (Delta.faceBoundary (Delta.toCombMap.faceOf x)).darts.length ∧
    ∃ a ∈ family, ∃ b ∈ family, a ≠ b ∧ Delta.toCombMap.faceOf x ∈ a.1 ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha x) ∈ b.1

/-- The number of region-pair darts. -/
noncomputable def regionPairCount (Delta : DiscDiagram.{u, w, v} W)
    (family : Finset (RegionCandidate D eps Delta)) : ℕ :=
  (Finset.univ.filter (IsRegionPairDart Delta family)).card

/-- No region-pair dart exactly when the count is zero. -/
theorem regionPairCount_eq_zero_iff (Delta : DiscDiagram.{u, w, v} W)
    (family : Finset (RegionCandidate D eps Delta)) :
    regionPairCount Delta family = 0 ↔ ∀ x, ¬ IsRegionPairDart Delta family x := by
  unfold regionPairCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h x
    exact h (Finset.mem_univ x)
  · intro h x _
    exact h x

/-- **Without region-pair darts, no edge joins two selected regions** (the field `regions` of
`PocketWalk.CopyClean` and of `CellPocketWalk.CopyClean`).  Let `x ≠ y` be regions of the family,
and suppose every edge from a face of `x` to a face of `y` has a face with at least two darts on
one side.  Without region-pair darts no such edge exists. -/
theorem regions_of_noRegionPairDart {Delta : DiscDiagram.{u, w, v} W}
    {family : Finset (RegionCandidate D eps Delta)}
    (hno : ∀ x, ¬ IsRegionPairDart Delta family x)
    {x y : RegionCandidate D eps Delta} (hx : x ∈ family) (hy : y ∈ family) (hxy : x ≠ y)
    (hmono : ∀ d, Delta.toCombMap.faceOf d ∈ x.1 →
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∈ y.1 →
        1 < (Delta.faceBoundary (Delta.toCombMap.faceOf d)).darts.length ∨
          1 < (Delta.faceBoundary
            (Delta.toCombMap.faceOf (Delta.toCombMap.alpha d))).darts.length) :
    ∀ d, Delta.toCombMap.faceOf d ∈ x.1 →
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∉ y.1 := by
  intro d hdx hdy
  rcases hmono d hdx hdy with h | h
  · exact hno d ⟨h, x, hx, y, hy, hxy, hdx, hdy⟩
  · refine hno (Delta.toCombMap.alpha d) ⟨h, y, hy, x, hx, hxy.symm, hdy, ?_⟩
    rw [Delta.toCombMap.alpha_involutive d]
    exact hdx

end GroupApproximation.GGT.VanKampen.RegionPairThickening

#audit_axioms GroupApproximation.GGT.VanKampen.RegionPairThickening.regionPairCount_eq_zero_iff
#audit_axioms GroupApproximation.GGT.VanKampen.RegionPairThickening.regions_of_noRegionPairDart
