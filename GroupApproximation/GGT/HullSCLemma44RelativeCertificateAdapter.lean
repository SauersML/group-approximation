import GroupApproximation.GGT.HullSCLemma44EmbeddedCertificate
import GroupApproximation.GGT.VanKampen.FaceSetPeelWitness
import GroupApproximation.GGT.VanKampen.SurgeryMap

/-!
# vk payloads for the relative Greendlinger certificate

The vk disc realization and its face-peeling construction expose planar data
at the dart level.  This file packages the exact fields needed by the
certificate consumer.  A payload gives a contiguity for each algebraic cell,
the linear boundary position, admissibility of the two connector words, a
face-peeling witness, and the disc-region surgery equality.  The constructor
below converts these fields to `RelativeDiagramCertificate`; later quotient
arguments use only that abstract certificate.

The source is Osin Lemma 4.4: the face-set pasting equation supplies the
cycle value, while the exterior estimate supplies the selected large cell.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded

universe u w

/-! ## One positioned vk cell -/

/-- All vk fields needed to turn one embedded boundary contiguity into a
`RelativeBoundaryContiguity`.  `position` is the linear before/arc/after
decomposition.  `peeling` supplies the value-one equation.  `surgery` names
the `SurgeryMap` disc collapse and `surgery_cycle` identifies its boundary
cycle with the selected contiguity cycle. -/
structure VkBoundaryCertificateData
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : RelativeReducedDiagram D W R)
    (hreal : RelativeDiscRealization D W Z)
    {eps : ℕ} {i : Fin hreal.diagram.rCellCount}
    (C : EmbeddedBoundaryContiguity D eps hreal.diagram i) where
  position : EmbeddedBoundaryPosition Z C
  leftSide_admissible : RelWord.IsAdmissible D
    (Embedded.dartWord hreal.diagram C.region.rightSide)
  rightSide_admissible : RelWord.IsAdmissible D
    (Embedded.dartWord hreal.diagram C.region.leftSide)
  peeling : Embedded.FaceSetBoundaryPeeling C.region.boundary
  surgery : Surgery.MapCollapse.IsDiscRegion hreal.diagram.toCombMap C.faces
  surgery_cycle : surgery.toBoundaryCycle.cycle = C.region.boundary.cycle
  cell_label_transport :
    Embedded.dartWord hreal.diagram C.region.sourceArc.rotated =
      (Z.cells.get (hreal.cellIndex.symm C.region.source)).relator

/-- The face-set witness form is accepted directly and expanded by the
finite face-count theorem.  This is the vk-facing spelling when a producer
supplies one `FaceSetBoundaryPeelWitness` for every current boundary. -/
theorem peeling_of_faceSetPeelWitness
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, 0} W}
    {faces : Finset Delta.toCombMap.Face}
    (boundary : Embedded.FaceSetBoundary Delta faces)
    (oracle : Embedded.FaceSetBoundaryPeelOracle (Delta := Delta)) :
    Embedded.FaceSetBoundaryPeeling boundary :=
  Embedded.faceSetBoundaryPeeling_of_faceSetBoundary_of_oracle boundary oracle

/-- A positioned vk payload gives the old embedded certificate data.  The
`SurgeryMap` cycle equality is used before the face-peeling value equation is
returned at the selected boundary cycle. -/
def VkBoundaryCertificateData.toEmbeddedData
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : RelativeReducedDiagram D W R)
    (hreal : RelativeDiscRealization D W Z)
    {eps : ℕ} {i : Fin hreal.diagram.rCellCount}
    {C : EmbeddedBoundaryContiguity D eps hreal.diagram i}
    (data : VkBoundaryCertificateData Z hreal C) :
    EmbeddedBoundaryCertificateData Z hreal C where
  position := data.position
  leftSide_admissible := data.leftSide_admissible
  rightSide_admissible := data.rightSide_admissible
  cell_label_transport := data.cell_label_transport
  cycle_value_one := by
    have hpeel := Embedded.FaceSetBoundaryPeeling.cycle_value_eq_one
      C.region.boundary data.peeling
    have hsurgery : GGT.RelLetter.listVal
        (Embedded.dartWord hreal.diagram data.surgery.toBoundaryCycle.cycle) = 1 := by
      rw [data.surgery_cycle]
      exact hpeel
    simpa only [data.surgery_cycle] using hsurgery

private noncomputable def vkRelativeContiguity
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : RelativeReducedDiagram D W R)
    (hreal : RelativeDiscRealization D W Z)
    (eps : ℕ) (i : Fin Z.cells.length)
    (C : EmbeddedBoundaryContiguity D eps hreal.diagram (hreal.cellIndex i))
    (data : VkBoundaryCertificateData Z hreal C) :
    RelativeBoundaryContiguity D eps Z.boundaryWord (Z.cells.get i).relator := by
  let B := RelativeBoundaryContiguity.of_embeddedData Z hreal C
    (data.toEmbeddedData Z hreal)
  have hlabel := data.cell_label_transport
  have hi : hreal.cellIndex.symm C.region.source = i := by
    rw [C.source_eq, hreal.cellIndex.symm_apply_apply]
  change RelativeBoundaryContiguity D eps Z.boundaryWord
    (Embedded.dartWord hreal.diagram C.region.sourceArc.rotated) at B
  rw [hi] at hlabel
  rw [hlabel] at B
  exact B

/-! ## A complete cell family -/

/-- A vk family payload has one optional positioned contiguity at each
algebraic cell and its converted relative contiguity.  `relative_eq` is the
single conversion equation required by the certificate consumer.  The
`large` field is measured on the converted exterior word, so no dart-level
cast remains in the final certificate. -/
structure VkRelativeDiagramCertificateData
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : RelativeReducedDiagram D W R)
    (hreal : RelativeDiscRealization D W Z)
    (eps : ℕ) (mu : ℝ) where
  embeddedContiguity : ∀ i : Fin Z.cells.length,
    Option (EmbeddedBoundaryContiguity D eps hreal.diagram (hreal.cellIndex i))
  data : ∀ (i : Fin Z.cells.length)
    (C : EmbeddedBoundaryContiguity D eps hreal.diagram (hreal.cellIndex i)),
    VkBoundaryCertificateData Z hreal C
  relativeContiguity : ∀ i : Fin Z.cells.length,
    Option (RelativeBoundaryContiguity D eps Z.boundaryWord
      (Z.cells.get i).relator)
  relative_eq : ∀ (i : Fin Z.cells.length)
    (C : EmbeddedBoundaryContiguity D eps hreal.diagram (hreal.cellIndex i)),
    embeddedContiguity i = some C →
      relativeContiguity i =
        some (vkRelativeContiguity Z hreal eps i C (data i C))
  large : ∃ (i : Fin Z.cells.length)
      (C : EmbeddedBoundaryContiguity D eps hreal.diagram (hreal.cellIndex i)),
      embeddedContiguity i = some C ∧
        (1 - 23 * mu) * ((Z.cells.get i).relator.length : ℝ) ≤
          (vkRelativeContiguity Z hreal eps i C (data i C)).exterior.length

/-- The complete vk payload converts to the abstract relative certificate.
Only `RelativeDiagramCertificate` is exposed to the quotient consumer. -/
noncomputable def relativeDiagramCertificate_of_vkData
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    {Z : RelativeReducedDiagram D W R}
    (hreal : RelativeDiscRealization D W Z)
    (payload : VkRelativeDiagramCertificateData Z hreal eps mu) :
    RelativeDiagramCertificate D W eps mu Z where
  boundaryWord := Z.boundaryWord
  boundaryWord_eq := rfl
  cellLabel := fun i => (Z.cells.get i).relator
  cellLabel_eq := fun i => rfl
  cellLabel_mem := fun i => (Z.cells.get i).relator_mem
  contiguity := payload.relativeContiguity
  largeCell := by
    obtain ⟨i, C, hC, hlarge⟩ := payload.large
    let Crel := vkRelativeContiguity Z hreal eps i C (payload.data i C)
    have hrel : payload.relativeContiguity i = some Crel := by
      exact payload.relative_eq i C hC
    refine ⟨i, Crel, hrel, ?_⟩
    exact hlarge

end HullSC
end GroupApproximation
