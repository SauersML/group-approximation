import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import Mathlib.Tactic.Group

/-!
# Boundary values of embedded G-cell regions

This module supplies the cancellation algebra for the G-cell regions in
Osin's Appendix Definition M.  Complete selected face boundaries may be
deleted because their values are one, and an immediately followed dart and
its `alpha`-reverse may be deleted because their labels are inverse.  The
resulting finite face-pasting relation preserves the value of a dart word.

For an embedded contiguity region, identity of its cyclic boundary value gives
the source/right/outer/left equation used by Hull's Lemma 4.9.  The orientation
is the one fixed in `Embedded.Contiguity.boundary_decomposition`: the source
arc occurs reverse-inverted on the boundary of the G-cell region.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open GroupApproximation.HullSC

universe u w v

namespace Embedded

/-! ## Elementary dart-word cancellations -/

/-- Reading the reverse darts in reverse order gives the reverse-inverse of
the original dart word. -/
theorem dartWord_reverse_alpha
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (darts : List Delta.toCombMap.Dart) :
    dartWord Delta (darts.reverse.map Delta.toCombMap.alpha) =
      RelWord.revInv (dartWord Delta darts) := by
  simp only [dartWord, List.map_map, List.map_reverse, RelWord.revInv]
  apply congrArg List.reverse
  apply List.map_congr_left
  intro d hd
  exact Delta.label_alpha d

/-- The value of a reverse-alpha dart list is the inverse of the original
dart-list value. -/
theorem listVal_dartWord_reverse_alpha
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (darts : List Delta.toCombMap.Dart) :
    GGT.RelLetter.listVal
        (dartWord Delta (darts.reverse.map Delta.toCombMap.alpha)) =
      (GGT.RelLetter.listVal (dartWord Delta darts))⁻¹ := by
  rw [dartWord_reverse_alpha, RelWord.listVal_revInv]

/-- Deleting an immediately followed dart and reverse dart preserves the
value of a dart list. -/
theorem listVal_dartWord_erase_alpha_pair
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (before after : List Delta.toCombMap.Dart)
    (d : Delta.toCombMap.Dart) :
    GGT.RelLetter.listVal
        (dartWord Delta
          (before ++ d :: Delta.toCombMap.alpha d :: after)) =
      GGT.RelLetter.listVal (dartWord Delta (before ++ after)) := by
  simp only [dartWord, List.map_append, List.map_cons,
    RelWord.listVal_append, RelWord.listVal_cons, Delta.label_alpha]
  cases hlabel : Delta.label d <;>
    simp [HullSC.RelWord.inv, GGT.RelLetter.val]

/-- Mapping labels over concatenated dart lists respects concatenation. -/
theorem dartWord_append
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (first second : List Delta.toCombMap.Dart) :
    dartWord Delta (first ++ second) =
      dartWord Delta first ++ dartWord Delta second := by
  simp only [dartWord, List.map_append]

/-! ## Face-pasting homotopy -/

/-- Finite word moves used when a planar union of faces is pasted into its
single exterior boundary.  A selected complete face and an immediate
`alpha`-pair are the two elementary deletions. -/
inductive FaceSetWordHomotopy
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (faces : Finset Delta.toCombMap.Face) :
    List Delta.toCombMap.Dart → List Delta.toCombMap.Dart → Prop
  | refl (word) : FaceSetWordHomotopy Delta faces word word
  | eraseFace (face : Delta.toCombMap.Face) (hface : face ∈ faces)
      (before after : List Delta.toCombMap.Dart) :
      FaceSetWordHomotopy Delta faces
        (before ++ (Delta.faceBoundary face).darts ++ after)
        (before ++ after)
  | eraseAlphaPair (dart : Delta.toCombMap.Dart)
      (before after : List Delta.toCombMap.Dart) :
      FaceSetWordHomotopy Delta faces
        (before ++ dart :: Delta.toCombMap.alpha dart :: after)
        (before ++ after)
  | symm {first second} :
      FaceSetWordHomotopy Delta faces first second →
        FaceSetWordHomotopy Delta faces second first
  | trans {first second third} :
      FaceSetWordHomotopy Delta faces first second →
      FaceSetWordHomotopy Delta faces second third →
        FaceSetWordHomotopy Delta faces first third

/-- Face-pasting moves preserve dart-word value when every selected face is a
G-cell. -/
theorem listVal_dartWord_eq_of_faceSetWordHomotopy
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (faces : Finset Delta.toCombMap.Face)
    (all_gCells : ∀ face ∈ faces,
      face ≠ Delta.outerFace ∧
        GGT.RelLetter.listVal (Delta.faceWord face) = 1)
    {first second : List Delta.toCombMap.Dart}
    (homotopy : FaceSetWordHomotopy Delta faces first second) :
    GGT.RelLetter.listVal (dartWord Delta first) =
      GGT.RelLetter.listVal (dartWord Delta second) := by
  induction homotopy with
  | refl => rfl
  | eraseFace face hface before after =>
      have hvalue : GGT.RelLetter.listVal
          (dartWord Delta (Delta.faceBoundary face).darts) = 1 := by
        simpa only [dartWord, DiscDiagram.faceWord] using
          (all_gCells face hface).2
      rw [dartWord_append, dartWord_append, RelWord.listVal_append,
        RelWord.listVal_append, hvalue]
      calc
        GGT.RelLetter.listVal (dartWord Delta before) * 1 *
              GGT.RelLetter.listVal (dartWord Delta after) =
            GGT.RelLetter.listVal (dartWord Delta before) *
              GGT.RelLetter.listVal (dartWord Delta after) := by
          group
        _ = GGT.RelLetter.listVal
            (dartWord Delta (before ++ after)) := by
          rw [dartWord_append, RelWord.listVal_append]
  | eraseAlphaPair dart before after =>
      exact listVal_dartWord_erase_alpha_pair Delta before after dart
  | symm _ ih => exact ih.symm
  | trans _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- A single-cycle G-cell face set has boundary value one once its cellular
pasting to the empty word is supplied. -/
theorem FaceSetBoundary.cycle_value_eq_one_of_pasting
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces)
    (pasting : FaceSetWordHomotopy Delta faces boundary.cycle []) :
    GGT.RelLetter.listVal (dartWord Delta boundary.cycle) = 1 := by
  have hvalue := listVal_dartWord_eq_of_faceSetWordHomotopy
    Delta faces boundary.all_gCells pasting
  simpa [dartWord, GGT.RelLetter.listVal] using hvalue

/-- A single-cycle `G`-region has boundary value one after its face-boundary
cycles and internal `alpha`-pairs are pasted away. -/
theorem FaceSetBoundary.cycle_value_eq_one
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces)
    (pasting : FaceSetWordHomotopy Delta faces boundary.cycle []) :
    GGT.RelLetter.listVal (dartWord Delta boundary.cycle) = 1 :=
  boundary.cycle_value_eq_one_of_pasting pasting

/-! ## The contiguity-region arc equation -/

/-- Identity of the cyclic G-region boundary gives the exact arc equation
used by the Hull Lemma 4.9 embedded-arc extractor. -/
theorem Contiguity.arcs_value_of_cycle_value_one
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (hcycle : GGT.RelLetter.listVal
      (dartWord Delta Gamma.boundary.cycle) = 1) :
    GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts) =
      GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide) *
        GGT.RelLetter.listVal
          (dartWord Delta
            (targetBoundaryDarts Delta Gamma.target Gamma.targetArc)) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide) := by
  have hdecomposition := Gamma.boundary_decomposition
  rw [hdecomposition, dartWord_append, dartWord_append, dartWord_append,
    RelWord.listVal_append, RelWord.listVal_append,
    RelWord.listVal_append] at hcycle
  have hreverse :
      GGT.RelLetter.listVal
          (dartWord Delta Gamma.sourceArc.reverseDarts) =
        (GGT.RelLetter.listVal
          (dartWord Delta Gamma.sourceArc.darts))⁻¹ := by
    exact listVal_dartWord_reverse_alpha Delta Gamma.sourceArc.darts
  rw [hreverse] at hcycle
  calc
    GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts) =
        GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts) * 1 := by
      group
    _ = GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts) *
        ((GGT.RelLetter.listVal
            (dartWord Delta Gamma.sourceArc.darts))⁻¹ *
          GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide) *
          GGT.RelLetter.listVal
            (dartWord Delta
              (targetBoundaryDarts Delta Gamma.target Gamma.targetArc)) *
          GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide)) := by
      rw [hcycle]
    _ = GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide) *
        GGT.RelLetter.listVal
          (dartWord Delta
            (targetBoundaryDarts Delta Gamma.target Gamma.targetArc)) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide) := by
      group

/-- A face-pasting certificate for the embedded G-region supplies its exact
source/right/target/left equation. -/
theorem Contiguity.arcs_value_of_pasting
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (pasting : FaceSetWordHomotopy Delta faces Gamma.boundary.cycle []) :
    GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts) =
      GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide) *
        GGT.RelLetter.listVal
          (dartWord Delta
            (targetBoundaryDarts Delta Gamma.target Gamma.targetArc)) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide) := by
  apply Gamma.arcs_value_of_cycle_value_one
  exact Gamma.boundary.cycle_value_eq_one_of_pasting pasting

end Embedded

end VanKampen
end GGT
end GroupApproximation
