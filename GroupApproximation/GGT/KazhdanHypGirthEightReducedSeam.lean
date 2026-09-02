import GroupApproximation.GGT.KazhdanHypGirthEightPrimitives2

/-!
# Reduced seams at vertices

The algebraic `DiscDiagram.Reduced` predicate forbids an ordered pair of
relator cells whose transported values cancel.  This file states the small
incidence certificate which identifies a mirror pair of corners in a seam
with such an ordered pair, and proves the cellular no-mirror conclusion.
The incidence certificate is the only local planar fact not exposed by the
ordered diagram API; once supplied, the proof is the direct Osin reduction
argument.
-/

namespace GroupApproximation
namespace GGT
namespace GirthEightPrimitives2

open GroupApproximation.KazhdanHyp
open VanKampen
open GirthEightVKInterface

universe u w v

variable {Generator TriangleIndex : Type}
  {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
  {W : Set (List (RelLetter (FreeGroup Generator) PEmpty))}

/-- A mirror corner pair is witnessed by two ordered relator cells and the
transported cancellation equation used by `DiscDiagram.Reduced`.  This is
strictly smaller than cellular reducedness: it only describes how a proposed
mirror in one cyclic corner enumeration is represented in the ordered cell
list. -/
structure ReducedMirrorIncidence
    (Delta : DiscDiagram.{u, w, 0} W)
    {vtx : Delta.toCombMap.Vertex}
    (C : CyclicCornerEnumeration Delta.toCombMap vtx)
    (K : VertexCornerCertificate (T := T)
      (C := C)) where
  mirror_to_ordered : ∀ i,
    K.linkVertex i = K.linkVertex (i + 2) →
      ∃ (pre between suf : List
          (RelatorCell Delta.toCombMap Delta.outerFace W))
        (C₁ C₂ : RelatorCell Delta.toCombMap Delta.outerFace W),
        Delta.relatorCells = pre ++ C₁ :: (between ++ C₂ :: suf) ∧
        (between.map RelatorCell.value).prod⁻¹ * C₁.value *
            (between.map RelatorCell.value).prod * C₂.value = 1

/-- Diagram-level reducedness excludes every mirror corner supplied by the
incidence certificate, so the cyclic seam walk is non-backtracking. -/
theorem cellularReducedAt_of_reduced
    (Delta : DiscDiagram.{u, w, 0} W)
    {vtx : Delta.toCombMap.Vertex}
    (C : CyclicCornerEnumeration Delta.toCombMap vtx)
    (K : VertexCornerCertificate (T := T) (C := C))
    (hred : Delta.Reduced)
    (I : ReducedMirrorIncidence Delta C K) :
    CellularReducedAt K := by
  intro i hmirror
  obtain ⟨pre, between, suf, C₁, C₂, hsplit, hcancel⟩ :=
    I.mirror_to_ordered i hmirror
  exact (hred pre between suf C₁ C₂ hsplit) hcancel

/-- The one-cell model has no ordered pair of relator cells, so the reduced
predicate is immediate and the preceding constructor is vacuous whenever its
incidence certificate is present. -/
theorem cellularReducedAt_of_oneCell_empty
    (Delta : DiscDiagram.{u, w, 0} W)
    (hzero : Delta.relatorCells = [])
    {vtx : Delta.toCombMap.Vertex}
    (C : CyclicCornerEnumeration Delta.toCombMap vtx)
    (K : VertexCornerCertificate (T := T) (C := C))
    (I : ReducedMirrorIncidence Delta C K) :
    CellularReducedAt K := by
  apply cellularReducedAt_of_reduced Delta C K
    (DiscDiagram.reduced_of_no_rCells Delta hzero) I

end GirthEightPrimitives2
end GGT
end GroupApproximation
