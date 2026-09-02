import GroupApproximation.GGT.VanKampen.FaceSetBoundaryRotation

/-!
# Exposed darts of a selected face set

This file proves the first planar ingredient for an extremal face peel.  In a
connected combinatorial map, every selected non-exterior face has a dart whose
reverse is based outside the selected set.  The proof follows a connectivity
path from a dart of that face to a dart of the exterior face and inducts on the
equivalence closure of the dart adjacency relation.  Both generators are
handled: `alpha` crosses the edge directly, while `sigma` crosses the edge
represented by `alpha d`, since `facePerm (alpha d) = sigma d`.

This is deliberately smaller than the full peel witness.  It supplies the
nonempty boundary arc endpoint; constructing the single-cycle remainder after
deleting an extremal face remains a separate surgery theorem.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open GroupApproximation.HullSC

universe u w v

namespace Embedded

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

noncomputable local instance faceDecidableEqExit :
    DecidableEq Delta.toCombMap.Face := Classical.decEq _

/-- Membership of the face under a dart in the selected face set. -/
private def selectedDart
    (faces : Finset Delta.toCombMap.Face) (d : Delta.toCombMap.Dart) : Prop :=
  Delta.toCombMap.faceOf d ∈ faces

private theorem faceOf_sigma
    (d : Delta.toCombMap.Dart) :
    Delta.toCombMap.faceOf (Delta.toCombMap.sigma d) =
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) := by
  have hface := Delta.toCombMap.faceOf_facePerm (Delta.toCombMap.alpha d)
  change Delta.toCombMap.faceOf
      (Delta.toCombMap.sigma (Delta.toCombMap.alpha
        (Delta.toCombMap.alpha d))) = _ at hface
  rw [Delta.toCombMap.alpha_involutive] at hface
  exact hface

private theorem boundary_of_selected_alpha
    {faces : Finset Delta.toCombMap.Face}
    {d : Delta.toCombMap.Dart}
    (hd : selectedDart faces d)
    (hda : ¬ selectedDart faces (Delta.toCombMap.alpha d)) :
    IsBoundaryDart Delta faces d :=
  ⟨hd, hda⟩

private theorem boundary_of_selected_alpha_reverse
    {faces : Finset Delta.toCombMap.Face}
    {d : Delta.toCombMap.Dart}
    (hd : selectedDart faces (Delta.toCombMap.alpha d))
    (hda : ¬ selectedDart faces d) :
    IsBoundaryDart Delta faces (Delta.toCombMap.alpha d) := by
  refine ⟨hd, ?_⟩
  rw [Delta.toCombMap.alpha_involutive]
  exact hda

/-! A single dart-adjacency edge with different selected statuses exposes a
boundary dart. -/

private theorem exists_boundary_of_adjacent_status_change
    {faces : Finset Delta.toCombMap.Face}
    {d e : Delta.toCombMap.Dart}
    (hde : Delta.toCombMap.Adjacent d e)
    (hstatus :
      (selectedDart faces d ∧ ¬ selectedDart faces e) ∨
      (¬ selectedDart faces d ∧ selectedDart faces e)) :
    ∃ q, IsBoundaryDart Delta faces q := by
  rcases hde with hα | hσ
  · subst e
    rcases hstatus with ⟨hd, hda⟩ | ⟨hd, hda⟩
    · exact ⟨d, boundary_of_selected_alpha hd hda⟩
    · exact ⟨Delta.toCombMap.alpha d,
        boundary_of_selected_alpha_reverse hda hd⟩
  · have hface : selectedDart faces e ↔
      selectedDart faces (Delta.toCombMap.alpha d) := by
      change Delta.toCombMap.faceOf e ∈ faces ↔
        Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∈ faces
      rw [← hσ, faceOf_sigma]
    rcases hstatus with ⟨hd, hde⟩ | ⟨hd, hde⟩
    · have hda : ¬ selectedDart faces (Delta.toCombMap.alpha d) := by
        intro hda
        exact hde (hface.mpr hda)
      exact ⟨d, boundary_of_selected_alpha hd hda⟩
    · have hda : selectedDart faces (Delta.toCombMap.alpha d) := by
        exact hface.mp hde
      exact ⟨Delta.toCombMap.alpha d,
        boundary_of_selected_alpha_reverse hda hd⟩

/-! The status-change lemma extends from a generating dart edge to its
equivalence closure. -/

private theorem exists_boundary_of_eqvGen_status_change
    {faces : Finset Delta.toCombMap.Face}
    {d e : Delta.toCombMap.Dart}
    (hde : Relation.EqvGen Delta.toCombMap.Adjacent d e)
    (hstatus :
      (selectedDart faces d ∧ ¬ selectedDart faces e) ∨
      (¬ selectedDart faces d ∧ selectedDart faces e)) :
    ∃ q, IsBoundaryDart Delta faces q := by
  induction hde with
  | rel d e hrel =>
      exact exists_boundary_of_adjacent_status_change hrel hstatus
  | refl d =>
      rcases hstatus with ⟨hd, he⟩ | ⟨hd, he⟩
      · exact (he hd).elim
      · exact (hd he).elim
  | symm d e hde ih =>
      rcases hstatus with ⟨hd, he⟩ | ⟨hd, he⟩
      · exact ih (.inr ⟨he, hd⟩)
      · exact ih (.inl ⟨he, hd⟩)
  | trans d e f hde hef ihde ihef =>
      rcases hstatus with ⟨hd, hf⟩ | ⟨hd, hf⟩
      · by_cases he : selectedDart faces e
        · exact ihef (.inl ⟨he, hf⟩)
        · exact ihde (.inl ⟨hd, he⟩)
      · by_cases he : selectedDart faces e
        · exact ihde (.inr ⟨hd, he⟩)
        · exact ihef (.inr ⟨he, hf⟩)

/-! ## Every selected face is exposed -/

/-- Every selected face of a `FaceSetBoundary` has an exposed dart. -/
theorem exists_boundary_dart_of_face_mem
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces)
    {face : Delta.toCombMap.Face} (hface : face ∈ faces) :
    ∃ d, IsBoundaryDart Delta faces d := by
  let source : Delta.toCombMap.Dart :=
    (Delta.faceBoundary face).darts.head (Delta.faceBoundary face).nonempty
  let exterior : Delta.toCombMap.Dart :=
    (Delta.faceBoundary Delta.outerFace).darts.head
      (Delta.faceBoundary Delta.outerFace).nonempty
  have hsource : Delta.toCombMap.faceOf source = face := by
    exact (Delta.faceBoundary face).mem_iff source |>.mp
      (List.head_mem (Delta.faceBoundary face).nonempty)
  have hexterior : Delta.toCombMap.faceOf exterior = Delta.outerFace := by
    exact (Delta.faceBoundary Delta.outerFace).mem_iff exterior |>.mp
      (List.head_mem (Delta.faceBoundary Delta.outerFace).nonempty)
  have hsource_selected : selectedDart faces source := by
    simpa [selectedDart, hsource] using hface
  have hexterior_not_selected : ¬ selectedDart faces exterior := by
    intro hselected
    have houter : Delta.outerFace ∈ faces := by
      simpa [selectedDart, hexterior] using hselected
    exact (boundary.all_gCells Delta.outerFace houter).1 rfl
  have hpath : Relation.EqvGen Delta.toCombMap.Adjacent source exterior :=
    Delta.planar.1 source exterior
  exact exists_boundary_of_eqvGen_status_change hpath
    (.inl ⟨hsource_selected, hexterior_not_selected⟩)

/-- The exposed dart belongs to the boundary cycle supplied by the estimating
record. -/
theorem exists_boundary_cycle_dart_of_face_mem
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces)
    {face : Delta.toCombMap.Face} (hface : face ∈ faces) :
    ∃ d, d ∈ boundary.cycle ∧ IsBoundaryDart Delta faces d := by
  obtain ⟨d, hd⟩ := exists_boundary_dart_of_face_mem boundary hface
  exact ⟨d, (boundary.cycle_mem_iff d).2 hd, hd⟩

/-! ## Model-facing corollaries -/

theorem exists_boundary_cycle_dart_oneFace
    {face : Delta.toCombMap.Face}
    {boundary : FaceSetBoundary Delta ({face} : Finset Delta.toCombMap.Face)} :
    ∃ d, d ∈ boundary.cycle ∧
      IsBoundaryDart Delta ({face} : Finset Delta.toCombMap.Face) d := by
  exact exists_boundary_cycle_dart_of_face_mem boundary (face := face) (by simp)

theorem exists_boundary_cycle_dart_twoFaces
    {f₁ f₂ : Delta.toCombMap.Face}
    {boundary : FaceSetBoundary Delta ({f₁, f₂} : Finset Delta.toCombMap.Face)}
    (h₁ : f₁ ∈ ({f₁, f₂} : Finset Delta.toCombMap.Face)) :
    ∃ d, d ∈ boundary.cycle ∧
      IsBoundaryDart Delta ({f₁, f₂} : Finset Delta.toCombMap.Face) d := by
  exact exists_boundary_cycle_dart_of_face_mem boundary h₁

theorem exists_boundary_cycle_dart_fourFaces
    {f₁ f₂ f₃ f₄ : Delta.toCombMap.Face}
    {boundary : FaceSetBoundary Delta
      ({f₁, f₂, f₃, f₄} : Finset Delta.toCombMap.Face)}
    (h₁ : f₁ ∈ ({f₁, f₂, f₃, f₄} : Finset Delta.toCombMap.Face)) :
    ∃ d, d ∈ boundary.cycle ∧
      IsBoundaryDart Delta ({f₁, f₂, f₃, f₄} : Finset Delta.toCombMap.Face) d := by
  exact exists_boundary_cycle_dart_of_face_mem boundary h₁

end Embedded
end VanKampen
end GGT
end GroupApproximation
