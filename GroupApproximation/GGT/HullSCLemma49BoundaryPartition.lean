import GroupApproximation.GGT.VanKampen.FaceSetPeelWitness
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryRotation
import Mathlib.Tactic

/-!
# Boundary-length accounting for Lemma 4.9

This file proves the finite-list part of the complementary-component
decomposition used in Hull's Lemma 4.9.  A `FaceSetBoundary` supplies the
boundary cycle, while its `IsBoundaryDart` predicate supplies the membership
certificate for each component and exterior arc.  A face-peel witness supplies
the corresponding cyclic arc factor.  The geometric producer still has to
construct the component lists and their length partition from a reduced disc
diagram; once it does so, the subtraction identity below is immediate from
`List.length` and finite sums.

The source is the boundary decomposition in Osin's Appendix Lemma 62 and the
cyclic boundary bookkeeping in the proof of Hull, Lemma 4.9.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Embedded

universe u w v

open GroupApproximation.HullSC

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

noncomputable local instance faceDecidableEqHullLemma49 :
    DecidableEq Delta.toCombMap.Face := Classical.decEq _

/-! ## The finite boundary certificate -/

/-- A finite complementary-component decomposition of a selected-face boundary.
The two families are lists of darts on the cycle.  The `IsBoundaryDart` fields
are the local map certificate; `length_partition` is the sole counting input
needed for the subtraction identity. -/
structure HullLemma49BoundaryLengthPartition
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces)
    (componentCount exteriorCount : ℕ) where
  components : Fin componentCount → List Delta.toCombMap.Dart
  exteriorArcs : Fin exteriorCount → List Delta.toCombMap.Dart
  components_boundary : ∀ (i : Fin componentCount)
    (dart : Delta.toCombMap.Dart),
    dart ∈ components i → IsBoundaryDart Delta faces dart
  exteriorArcs_boundary : ∀ (i : Fin exteriorCount)
    (dart : Delta.toCombMap.Dart),
    dart ∈ exteriorArcs i → IsBoundaryDart Delta faces dart
  length_partition :
    boundary.cycle.length =
      (∑ i : Fin componentCount, (components i).length) +
        ∑ i : Fin exteriorCount, (exteriorArcs i).length

/-- The local map certificates put every component dart on the enumerated
boundary cycle. -/
theorem HullLemma49BoundaryLengthPartition.components_mem_cycle
    {faces : Finset Delta.toCombMap.Face}
    {boundary : FaceSetBoundary Delta faces}
    {componentCount exteriorCount : ℕ}
    (certificate : HullLemma49BoundaryLengthPartition boundary
      componentCount exteriorCount)
    (i : Fin componentCount) (dart : Delta.toCombMap.Dart)
    (hdart : dart ∈ certificate.components i) :
    dart ∈ boundary.cycle := by
  exact (boundary.cycle_mem_iff dart).2
    (certificate.components_boundary i dart hdart)

/-- The local map certificates put every selected exterior dart on the
enumerated boundary cycle. -/
theorem HullLemma49BoundaryLengthPartition.exteriorArcs_mem_cycle
    {faces : Finset Delta.toCombMap.Face}
    {boundary : FaceSetBoundary Delta faces}
    {componentCount exteriorCount : ℕ}
    (certificate : HullLemma49BoundaryLengthPartition boundary
      componentCount exteriorCount)
    (i : Fin exteriorCount) (dart : Delta.toCombMap.Dart)
    (hdart : dart ∈ certificate.exteriorArcs i) :
    dart ∈ boundary.cycle := by
  exact (boundary.cycle_mem_iff dart).2
    (certificate.exteriorArcs_boundary i dart hdart)

/-! ## The list and finite-sum identity -/

/-- The finite-list boundary accounting statement needed by the
complementary-component producer. -/
def HullLemma49BoundaryLengthStatement : Prop :=
  ∀ {alpha : Type u} {componentCount exteriorCount : ℕ}
    (cycle : List alpha)
    (components : Fin componentCount → List alpha)
    (exteriorArcs : Fin exteriorCount → List alpha),
    cycle.length =
      (∑ i : Fin componentCount, (components i).length) +
        ∑ i : Fin exteriorCount, (exteriorArcs i).length →
    (∑ i : Fin componentCount, (components i).length) =
      cycle.length - ∑ i : Fin exteriorCount, (exteriorArcs i).length

/-- The finite-list boundary accounting statement follows from natural-number
subtraction after the length partition. -/
theorem hullLemma49BoundaryLengthStatement :
    HullLemma49BoundaryLengthStatement := by
  intro alpha componentCount exteriorCount cycle components exteriorArcs
    hpartition
  omega

/-- If a cycle length is the sum of component and exterior-arc lengths, the
component sum is the cycle length minus the exterior-arc sum. -/
theorem hullLemma49ListLength_component_sum_eq_sub
    {alpha : Type u} {componentCount exteriorCount : ℕ}
    (cycle : List alpha)
    (components : Fin componentCount → List alpha)
    (exteriorArcs : Fin exteriorCount → List alpha)
    (hpartition :
      cycle.length =
        (∑ i : Fin componentCount, (components i).length) +
          ∑ i : Fin exteriorCount, (exteriorArcs i).length) :
    (∑ i : Fin componentCount, (components i).length) =
      cycle.length - ∑ i : Fin exteriorCount, (exteriorArcs i).length := by
  exact hullLemma49BoundaryLengthStatement cycle components exteriorArcs
    hpartition

/-- The boundary-cycle version of the finite-list identity.  This is the
single counting statement for which the complementary-component producer
must supply a certificate. -/
theorem hullLemma49BoundaryLength_component_sum_eq_sub
    {faces : Finset Delta.toCombMap.Face}
    {boundary : FaceSetBoundary Delta faces}
    {componentCount exteriorCount : ℕ}
    (certificate : HullLemma49BoundaryLengthPartition boundary
      componentCount exteriorCount) :
    (∑ i : Fin componentCount, (certificate.components i).length) =
      boundary.cycle.length -
        ∑ i : Fin exteriorCount, (certificate.exteriorArcs i).length := by
  exact hullLemma49ListLength_component_sum_eq_sub boundary.cycle
    certificate.components certificate.exteriorArcs certificate.length_partition

/-! ## Compatibility with the landed cyclic boundary machinery -/

/-- Rotating the base dart preserves the cycle length. -/
@[simp] theorem hullLemma49BoundaryLength_rotate_cycle
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces) (k : ℕ) :
    (boundary.rotate k).cycle.length = boundary.cycle.length := by
  rw [FaceSetBoundary.rotate_cycle, List.length_rotate]

/-- A boundary-length certificate transports across a change of cyclic
basepoint.  Membership remains `IsBoundaryDart`, and the length equation uses
the rotation-length equality. -/
def HullLemma49BoundaryLengthPartition.rotate
    {faces : Finset Delta.toCombMap.Face}
    {componentCount exteriorCount : ℕ}
    {boundary : FaceSetBoundary Delta faces}
    (certificate : HullLemma49BoundaryLengthPartition boundary
      componentCount exteriorCount) (k : ℕ) :
    HullLemma49BoundaryLengthPartition (boundary.rotate k)
      componentCount exteriorCount where
  components := certificate.components
  exteriorArcs := certificate.exteriorArcs
  components_boundary := certificate.components_boundary
  exteriorArcs_boundary := certificate.exteriorArcs_boundary
  length_partition := by
    rw [hullLemma49BoundaryLength_rotate_cycle]
    exact certificate.length_partition

/-- The component subtraction identity is invariant under the chosen
basepoint. -/
theorem hullLemma49BoundaryLength_rotate_component_sum_eq_sub
    {faces : Finset Delta.toCombMap.Face}
    {boundary : FaceSetBoundary Delta faces}
    {componentCount exteriorCount : ℕ}
    (certificate : HullLemma49BoundaryLengthPartition boundary
      componentCount exteriorCount) (k : ℕ) :
    (∑ i : Fin componentCount,
        ((certificate.rotate k).components i).length) =
      (boundary.rotate k).cycle.length -
        ∑ i : Fin exteriorCount,
          ((certificate.rotate k).exteriorArcs i).length := by
  exact hullLemma49BoundaryLength_component_sum_eq_sub
    (certificate.rotate k)

/-! ## Peeling and model checks -/

/-- The arc factor in a face-peel witness gives an explicit length split of
the current boundary cycle. -/
theorem hullLemma49PeelWitness_arc_length_split
    {faces : Finset Delta.toCombMap.Face}
    {boundary : FaceSetBoundary Delta faces}
    (witness : FaceSetBoundaryPeelWitness boundary) :
    ∃ before after : List Delta.toCombMap.Dart,
      boundary.cycle.length = before.length + witness.arc.length + after.length := by
  obtain ⟨before, after, hfactor⟩ := witness.arc_factor
  refine ⟨before, after, ?_⟩
  rw [hfactor]
  simp [List.length_append, Nat.add_assoc]

/-- One cell has one unbound component, namely the part left after its exterior
arc is removed.  The identity is the exact `Finset.sum` form used by the
partition certificate. -/
theorem hullLemma49BoundaryLength_oneCell_model
    {alpha : Type u} (component exterior : List alpha) :
    (∑ i : Fin 1, ((fun _ : Fin 1 => component) i).length) =
        (component ++ exterior).length -
          ∑ i : Fin 1, ((fun _ : Fin 1 => exterior) i).length := by
  have hpartition :
      (component ++ exterior).length =
        (∑ i : Fin 1, ((fun _ : Fin 1 => component) i).length) +
          ∑ i : Fin 1, ((fun _ : Fin 1 => exterior) i).length := by
    simp [List.length_append]
  exact hullLemma49ListLength_component_sum_eq_sub
    (component ++ exterior)
    (fun _ : Fin 1 => component)
    (fun _ : Fin 1 => exterior) hpartition

/-- Two mirror cells have two complementary components.  Their two lengths
are summed before the selected exterior arc is subtracted. -/
theorem hullLemma49BoundaryLength_twoCell_mirror_model
    {alpha : Type u} (left right exterior : List alpha) :
    (∑ i : Fin 2,
        (if (i : ℕ) = 0 then left else right).length) =
      (left ++ right ++ exterior).length -
        ∑ i : Fin 1, ((fun _ : Fin 1 => exterior) i).length := by
  have hpartition :
      (left ++ right ++ exterior).length =
        (∑ i : Fin 2,
          (if (i : ℕ) = 0 then left else right).length) +
          ∑ i : Fin 1, ((fun _ : Fin 1 => exterior) i).length := by
    rw [Fin.sum_univ_two]
    simp [List.length_append, Nat.add_assoc]
  exact hullLemma49ListLength_component_sum_eq_sub
    (left ++ right ++ exterior)
    (fun i : Fin 2 => if (i : ℕ) = 0 then left else right)
    (fun _ : Fin 1 => exterior) hpartition

/-- The one-cell peel witness exposes the same whole-cycle-minus-cell-arc
model used by the boundary count. -/
theorem hullLemma49PeelWitness_oneCell_model
    {face : Delta.toCombMap.Face}
    {boundary : FaceSetBoundary Delta ({face} : Finset Delta.toCombMap.Face)}
    (hcycle : boundary.cycle = (Delta.faceBoundary face).darts)
    (hne : face ≠ Delta.outerFace) :
    ∃ before after : List Delta.toCombMap.Dart,
      boundary.cycle.length = before.length +
        (faceSetBoundaryPeelWitness_of_planar boundary
          (oneFace_planarCertificate hcycle hne)).arc.length + after.length := by
  exact hullLemma49PeelWitness_arc_length_split
    (faceSetBoundaryPeelWitness_of_planar boundary
      (oneFace_planarCertificate hcycle hne))

/-- The two-cell mirror model exposes a boundary arc split after the first
face is peeled. -/
theorem hullLemma49PeelWitness_twoCell_mirror_model
    {faces : Finset Delta.toCombMap.Face}
    {f₁ f₂ : Delta.toCombMap.Face}
    (hfaces : faces = {f₁, f₂})
    (hneq : f₁ ≠ f₂)
    (h₁ : f₁ ≠ Delta.outerFace)
    (h₁mem : f₁ ∈ faces)
    (boundary : FaceSetBoundary Delta faces)
    (cycle next : List Delta.toCombMap.Dart)
    (hcycle : boundary.cycle = cycle)
    (moves : FaceSetMoveSequence (faces := faces) cycle next)
    (hcycle₂ : ∃ boundary : FaceSetBoundary Delta ({f₂} : Finset _),
      boundary.cycle = next) :
    ∃ before after : List Delta.toCombMap.Dart,
      boundary.cycle.length = before.length +
        (faceSetBoundaryPeelWitness_of_planar boundary
          (Classical.choice
            (twoFace_planarCertificate hfaces hneq h₁ h₁mem boundary cycle next
              hcycle moves hcycle₂))).arc.length + after.length := by
  exact hullLemma49PeelWitness_arc_length_split
    (faceSetBoundaryPeelWitness_of_planar boundary
      (Classical.choice
        (twoFace_planarCertificate hfaces hneq h₁ h₁mem boundary cycle next
          hcycle moves hcycle₂)))

end Embedded
end VanKampen
end GGT
end GroupApproximation
