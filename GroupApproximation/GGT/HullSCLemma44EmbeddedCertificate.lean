import GroupApproximation.GGT.VanKampen.RelativeDiscRealization
import GroupApproximation.GGT.VanKampen.FaceSetWordHomotopy
import GroupApproximation.GGT.VanKampen.Estimating.PieceBridge

/-!
# Embedded-to-relative certificates for Hull Lemma 4.4

The estimating construction produces a cyclic contiguity in a planar disc.
Hull's quotient consumer uses a based relative contiguity: its outer arc is a
linear subword of the designated boundary, its two sides are admissible
relative words, and its exterior value is the product of the two sides and
the outer arc.  This file states the small bridge between those interfaces.

The bridge asks only for data not exposed by the generic planar record:
face-set peeling supplies the value-one equation, a boundary-position witness
linearizes the outer cyclic arc, and admissibility witnesses type the two side
words.  The resulting theorem builds the complete finite certificate, putting
the supplied contiguity at one cell and using empty options elsewhere.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT.VanKampen
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u w

/-! ## The missing positioning and typing data -/

/-- A cyclic outer arc is identified with a based subword of the algebraic
boundary.  The value equation is stated separately because the planar
boundary is written in relative letters while the algebraic boundary is a
word in G. -/
structure EmbeddedBoundaryPosition
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R : ℕ} (Z : RelativeReducedDiagram D W R)
    {eps : ℕ} {Delta : DiscDiagram.{u, w, 0} W}
    (contiguity : EmbeddedBoundaryContiguity D eps Delta i) where
  boundaryBefore : List G
  boundaryArc : List G
  boundaryAfter : List G
  boundary_decomposition : Z.boundaryWord =
    boundaryBefore ++ boundaryArc ++ boundaryAfter
  outer_value : boundaryArc.prod =
    GGT.RelLetter.listVal (Embedded.dartWord Delta
      (contiguity.region.targetArc.darts))

/-- The side-word and face-pasting package needed for a relative contiguity. -/
structure EmbeddedBoundaryCertificateData
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R : ℕ} (Z : RelativeReducedDiagram D W R)
    {eps : ℕ} {Delta : DiscDiagram.{u, w, 0} W}
    (contiguity : EmbeddedBoundaryContiguity D eps Delta i) where
  position : EmbeddedBoundaryPosition Z contiguity
  leftSide_admissible : RelWord.IsAdmissible D
    (Embedded.dartWord Delta contiguity.region.rightSide)
  rightSide_admissible : RelWord.IsAdmissible D
    (Embedded.dartWord Delta contiguity.region.leftSide)
  peeling : Embedded.FaceSetBoundaryPeeling contiguity.region.boundary

/-! ## A positioned outer region gives a based contiguity -/

/-- The selected planar region yields the exact based contiguity.
The source exterior is the forward cyclic source arc; the connector names are
swapped because the planar boundary is traversed in reverse source, right,
outer, left order. -/
theorem RelativeBoundaryContiguity.of_embeddedData
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {R : ℕ} (Z : RelativeReducedDiagram D W R)
    (hreal : RelativeDiscRealization D W Z)
    {i : Fin hreal.diagram.rCellCount}
    (C : EmbeddedBoundaryContiguity D eps hreal.diagram i)
    (data : EmbeddedBoundaryCertificateData Z C)
    (j : Fin Z.cells.length)
    (hji : hreal.cellIndex j = C.region.source) :
    RelativeBoundaryContiguity D eps Z.boundaryWord
      (Z.cells.get j).relator := by
  let sourceArc := C.region.sourceArc
  obtain ⟨remainder, hsource⟩ := sourceArc.exists_dartWord_suffix
  have hcell : (Z.cells.get j).relator =
      Embedded.dartWord hreal.diagram sourceArc.rotated := by
    have hword := hreal.cellWord_eq j
    rw [hji] at hword
    rw [← hword]
    symm
    rw [Embedded.dartWord_cellDarts hreal.diagram C.region.source]
    exact (sourceArc.dartWord_rotated).symm
  have hsourceValue := C.region.arcs_value_of_pasting
    data.peeling.to_homotopy
  have hsourceValue' : GGT.RelLetter.listVal
      (Embedded.dartWord hreal.diagram sourceArc.darts) =
      GGT.RelLetter.listVal
        (Embedded.dartWord hreal.diagram C.region.rightSide) *
      data.position.boundaryArc.prod *
      GGT.RelLetter.listVal
        (Embedded.dartWord hreal.diagram C.region.leftSide) := by
    rw [data.position.outer_value] at hsourceValue
    exact hsourceValue
  let B0 : RelativeBoundaryContiguity D eps Z.boundaryWord
      (Embedded.dartWord hreal.diagram sourceArc.rotated) := {
    exterior := Embedded.dartWord hreal.diagram sourceArc.darts
    remainder := remainder
    relator_decomposition := hsource
    boundaryBefore := data.position.boundaryBefore
    boundaryArc := data.position.boundaryArc
    boundaryAfter := data.position.boundaryAfter
    boundary_decomposition := data.position.boundary_decomposition
    leftSide := Embedded.dartWord hreal.diagram C.region.rightSide
    rightSide := Embedded.dartWord hreal.diagram C.region.leftSide
    leftSide_admissible := data.leftSide_admissible
    rightSide_admissible := data.rightSide_admissible
    leftSide_short := C.region.rightSide_length_le
    rightSide_short := C.region.leftSide_length_le
    exterior_value := hsourceValue' }
  simpa only [hcell] using B0

/-! ## Certificate assembly -/

/-- A single embedded boundary contiguity becomes a certificate at the
corresponding algebraic cell. -/
theorem RelativeDiagramCertificate.of_embeddedData
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {mu : ℝ}
    {R : ℕ} (Z : RelativeReducedDiagram D W R)
    (hreal : RelativeDiscRealization D W Z)
    {i : Fin hreal.diagram.rCellCount}
    (C : EmbeddedBoundaryContiguity D eps hreal.diagram i)
    (data : EmbeddedBoundaryCertificateData Z C)
    (j : Fin Z.cells.length)
    (hji : hreal.cellIndex j = C.region.source)
    (hlarge : (1 - 13 * mu) *
        ((Embedded.cell hreal.diagram i).word.length : ℝ) <
        (C.region.sourceArc.length : ℝ)) :
    RelativeDiagramCertificate D W eps mu Z := by
  let B : RelativeBoundaryContiguity D eps Z.boundaryWord
      (Z.cells.get j).relator :=
    RelativeBoundaryContiguity.of_embeddedData Z hreal C data j hji
  have hcellLength : (Z.cells.get j).relator.length =
      C.region.sourceArc.length := by
    have hword := hreal.cellWord_eq j
    rw [hji] at hword
    have hsourceLength :
        (Embedded.dartWord hreal.diagram C.region.sourceArc.rotated).length =
          C.region.sourceArc.length := by
      simp only [Embedded.dartWord, List.length_map,
        C.region.sourceArc.rotated_length]
    rw [← hword, Embedded.dartWord_cellDarts hreal.diagram
      C.region.source, C.region.sourceArc.dartWord_rotated]
    exact hsourceLength
  have hlarge' : (1 - 23 * mu) *
      ((Z.cells.get j).relator.length : ℝ) ≤
      (B.exterior.length : ℝ) := by
    have hsourceLength' : B.exterior.length =
        C.region.sourceArc.length := by
      rfl
    rw [hsourceLength', hcellLength]
    have hcoeff : 1 - 23 * mu ≤ 1 - 13 * mu := by linarith
    have hnonneg : (0 : ℝ) ≤ (Z.cells.get j).relator.length := by
      positivity
    have hcoeffMul := mul_le_mul_of_nonneg_right hcoeff hnonneg
    linarith
  let labels : Fin Z.cells.length → List (GGT.RelLetter G Lambda) :=
    fun l => (Z.cells.get l).relator
  let options : ∀ l : Fin Z.cells.length,
      Option (RelativeBoundaryContiguity D eps Z.boundaryWord (labels l)) :=
    fun l => if hl : l = j then some (hji ▸ B) else none
  refine {
    boundaryWord := Z.boundaryWord
    boundaryWord_eq := rfl
    cellLabel := labels
    cellLabel_eq := fun l => rfl
    cellLabel_mem := fun l => (Z.cells.get l).relator_mem
    contiguity := options
    largeCell := ?_ }
  refine ⟨j, hji ▸ B, ?_, ?_⟩
  · dsimp [options]
    simp
  · simpa only [labels] using hlarge'

end HullSC
end GroupApproximation
