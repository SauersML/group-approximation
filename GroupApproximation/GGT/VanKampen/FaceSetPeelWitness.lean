import GroupApproximation.GGT.VanKampen.FaceSetBoundaryPeeling

/-!
# Planar face-peel certificates

This file separates the map-topology part of a face peel from the finite word
induction.  A `PlanarFacePeelCertificate` names an extremal selected face, a
nonempty arc of the current boundary, the finite insertion/`alpha`-cancellation
sequence exposing the remaining cycle, and the boundary certificate for that
remainder.  Its conversion to `FaceSetBoundaryPeelWitness` is immediate, and
`faceSetBoundaryPeeling_of_faceSetBoundary_of_oracle` then gives termination by
the number of selected faces.

The existing `FaceSetBoundary` record has no base dart for its cyclic list and
no field giving the remainder after an extremal deletion.  Consequently the
map-topology producer must provide the certificate below (or enrich the record
with equivalent data); the conversion and all finite termination are proved
here without an additional global schedule assumption.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Embedded

open GroupApproximation.HullSC

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

noncomputable local instance faceDecidableEqPeelWitness :
    DecidableEq Delta.toCombMap.Face := Classical.decEq _

/-- The one-step planar information needed to peel a selected face.  The
`moves` field is where a face boundary is inserted and all internal paired
darts are cancelled; `remainder` supplies the next single-cycle boundary. -/
structure PlanarFacePeelCertificate
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces) where
  face : Delta.toCombMap.Face
  face_mem : face ∈ faces
  face_ne_outer : face ≠ Delta.outerFace
  next : List Delta.toCombMap.Dart
  arc : List Delta.toCombMap.Dart
  arc_nonempty : arc ≠ []
  arc_factor : ∃ before after : List Delta.toCombMap.Dart,
    boundary.cycle = before ++ arc ++ after
  moves : FaceSetMoveSequence (faces := faces) boundary.cycle next
  remainder :
    (faces.erase face = ∅ ∧ next = []) ∨
      ∃ boundary' : FaceSetBoundary Delta (faces.erase face),
        boundary'.cycle = next

/-- A planar one-step certificate is exactly the local witness consumed by the
finite face-count induction. -/
def PlanarFacePeelCertificate.to_witness
    {faces : Finset Delta.toCombMap.Face}
    {boundary : FaceSetBoundary Delta faces}
    (certificate : PlanarFacePeelCertificate boundary) :
    FaceSetBoundaryPeelWitness boundary :=
  { face := certificate.face
    face_mem := certificate.face_mem
    face_ne_outer := certificate.face_ne_outer
    next := certificate.next
    arc := certificate.arc
    arc_nonempty := certificate.arc_nonempty
    arc_factor := certificate.arc_factor
    moves := certificate.moves
    remainder := certificate.remainder }

/-- The requested VK-side conversion from a planar extremal-face certificate
to a peel witness. -/
def faceSetBoundaryPeelWitness_of_planarCertificate
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces)
    (certificate : PlanarFacePeelCertificate boundary) :
    FaceSetBoundaryPeelWitness boundary :=
  certificate.to_witness

/-- A family of extremal planar certificates supplies the local oracle used by
the finite termination theorem. -/
theorem faceSetBoundaryPeeling_of_planarCertificates
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces)
    (certificates : ∀ {faces : Finset Delta.toCombMap.Face}
      (boundary : FaceSetBoundary Delta faces),
      PlanarFacePeelCertificate boundary) :
    FaceSetBoundaryPeeling boundary := by
  apply faceSetBoundaryPeeling_of_faceSetBoundary_of_oracle boundary
  intro faces boundary
  exact (certificates boundary).to_witness

/-! ## Model certificates -/

/-- One face, with its boundary list based at the same dart, is the direct
face-erasure model. -/
def oneFace_planarCertificate
    {face : Delta.toCombMap.Face}
    {boundary : FaceSetBoundary Delta ({face} : Finset Delta.toCombMap.Face)}
    (hcycle : boundary.cycle = (Delta.faceBoundary face).darts)
    (hne : face ≠ Delta.outerFace) :
    PlanarFacePeelCertificate boundary where
  face := face
  face_mem := by simp
  face_ne_outer := hne
  next := []
  arc := boundary.cycle
  arc_nonempty := by rw [hcycle]; exact (Delta.faceBoundary face).nonempty
  arc_factor := ⟨[], [], by simp⟩
  moves := by
    rw [hcycle]
    simpa only [List.nil_append, List.append_nil] using
      (FaceSetMoveSequence.cons
        (FaceSetElementaryMove.eraseFace face (by simp) [] [])
        (FaceSetMoveSequence.refl []))
  remainder := by
    left
    simp

/-- Two selected faces, including the adjacent-face case, reduce by the
explicit first move sequence and the one-face remainder. -/
theorem twoFace_planarCertificate
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
    Nonempty (PlanarFacePeelCertificate boundary) := by
  obtain ⟨boundary₂, hboundary₂⟩ := hcycle₂
  have hmem : f₁ ∈ faces := by
    simp [hfaces, hneq]
  refine ⟨{ face := f₁, face_mem := hmem,
    face_ne_outer := h₁, next := next, arc := cycle, arc_nonempty := ?_,
    arc_factor := ⟨[], [], by simp⟩, moves := ?_, remainder := ?_ }⟩
  · intro hnil
    apply boundary.cycle_nonempty
    rw [hcycle, hnil]
  · simpa [hcycle] using moves
  · right
    refine ⟨boundary₂, hboundary₂⟩

end Embedded
end VanKampen
end GGT
end GroupApproximation
