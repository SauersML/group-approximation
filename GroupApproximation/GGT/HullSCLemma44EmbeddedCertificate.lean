import GroupApproximation.GGT.VanKampen.RelativeDiscRealization
import GroupApproximation.GGT.VanKampen.RelativeGreendlinger

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
words.  The resulting definition turns this supplied local data into the based
relative contiguity consumed by the quotient arguments.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT.VanKampen
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u w

private theorem exists_dartWord_suffix_for_arc
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, 0} W}
    {cycle : List Delta.toCombMap.Dart}
    (arc : Embedded.CyclicArc cycle) :
    ∃ suffix : List (GGT.RelLetter G Lambda),
      Embedded.dartWord Delta arc.rotated =
        Embedded.dartWord Delta arc.darts ++ suffix := by
  refine ⟨Embedded.dartWord Delta (arc.rotated.drop arc.length), ?_⟩
  rw [Embedded.CyclicArc.darts]
  conv_lhs => rw [← List.take_append_drop arc.length arc.rotated]
  simp only [Embedded.dartWord, List.map_append, List.map_take,
    List.map_drop]

private theorem dartWord_reverse_alpha_for_arc
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, 0} W}
    (darts : List Delta.toCombMap.Dart) :
    Embedded.dartWord Delta
        (darts.reverse.map Delta.toCombMap.alpha) =
      RelWord.revInv (Embedded.dartWord Delta darts) := by
  simp only [Embedded.dartWord, List.map_map, List.map_reverse,
    RelWord.revInv]
  apply congrArg List.reverse
  apply List.map_congr_left
  intro d hd
  exact Delta.label_alpha d

private theorem dartWord_append_for_arc
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, 0} W}
    (first second : List Delta.toCombMap.Dart) :
    Embedded.dartWord Delta (first ++ second) =
      Embedded.dartWord Delta first ++ Embedded.dartWord Delta second := by
  simp only [Embedded.dartWord, List.map_append]

private theorem targetBoundaryDarts_eq_darts_for_none
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, 0} W}
    {target : Option (Fin Delta.rCellCount)}
    (arc : Embedded.CyclicArc (Embedded.targetDarts Delta target))
    (htarget : target = none) :
    Embedded.targetBoundaryDarts Delta target arc = arc.darts := by
  cases target with
  | none => rfl
  | some target => simp at htarget

private theorem arcs_value_of_cycle_value_one
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, 0} W}
    {faces : Finset Delta.toCombMap.Face}
    (C : Embedded.Contiguity D eps Delta faces)
    (hcycle : GGT.RelLetter.listVal
      (Embedded.dartWord Delta C.boundary.cycle) = 1) :
    GGT.RelLetter.listVal
        (Embedded.dartWord Delta C.sourceArc.darts) =
      GGT.RelLetter.listVal (Embedded.dartWord Delta C.rightSide) *
        GGT.RelLetter.listVal
          (Embedded.dartWord Delta
            (Embedded.targetBoundaryDarts Delta C.target C.targetArc)) *
        GGT.RelLetter.listVal (Embedded.dartWord Delta C.leftSide) := by
  rw [C.boundary_decomposition] at hcycle
  rw [dartWord_append_for_arc, dartWord_append_for_arc,
    dartWord_append_for_arc, RelWord.listVal_append,
    RelWord.listVal_append, RelWord.listVal_append] at hcycle
  have hreverse :
      GGT.RelLetter.listVal
          (Embedded.dartWord Delta C.sourceArc.reverseDarts) =
        (GGT.RelLetter.listVal
          (Embedded.dartWord Delta C.sourceArc.darts))⁻¹ := by
    change GGT.RelLetter.listVal
        (Embedded.dartWord Delta
          (C.sourceArc.darts.reverse.map Delta.toCombMap.alpha)) =
      _
    rw [dartWord_reverse_alpha_for_arc, RelWord.listVal_revInv]
  rw [hreverse] at hcycle
  calc
    GGT.RelLetter.listVal (Embedded.dartWord Delta C.sourceArc.darts) =
        GGT.RelLetter.listVal (Embedded.dartWord Delta C.sourceArc.darts) * 1 := by
      group
    _ = GGT.RelLetter.listVal (Embedded.dartWord Delta C.sourceArc.darts) *
        ((GGT.RelLetter.listVal
            (Embedded.dartWord Delta C.sourceArc.darts))⁻¹ *
          GGT.RelLetter.listVal (Embedded.dartWord Delta C.rightSide) *
          GGT.RelLetter.listVal
            (Embedded.dartWord Delta
              (Embedded.targetBoundaryDarts Delta C.target C.targetArc)) *
          GGT.RelLetter.listVal
            (Embedded.dartWord Delta C.leftSide)) := by
      rw [hcycle]
    _ = GGT.RelLetter.listVal (Embedded.dartWord Delta C.rightSide) *
        GGT.RelLetter.listVal
          (Embedded.dartWord Delta
            (Embedded.targetBoundaryDarts Delta C.target C.targetArc)) *
        GGT.RelLetter.listVal (Embedded.dartWord Delta C.leftSide) := by
      group

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
    {i : Fin Delta.rCellCount}
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
    (hreal : RelativeDiscRealization D W Z)
    {eps : ℕ}
    {i : Fin hreal.diagram.rCellCount}
    (contiguity : EmbeddedBoundaryContiguity D eps hreal.diagram i) where
  /-- The outer dart cycle is read from a linear position in the designated
  boundary word, with the displayed three-piece decomposition. -/
  position : EmbeddedBoundaryPosition Z contiguity
  /-- The two connector paths are relative words of length at most `eps`; the
  planar right side is the based left connector and the planar left side is
  the based right connector. -/
  leftSide_admissible : RelWord.IsAdmissible D
    (Embedded.dartWord hreal.diagram contiguity.region.rightSide)
  rightSide_admissible : RelWord.IsAdmissible D
    (Embedded.dartWord hreal.diagram contiguity.region.leftSide)
  /-- The positioned cyclic source arc has the algebraic relator label at the
  corresponding source-cell index. -/
  cell_label_transport :
    Embedded.dartWord hreal.diagram contiguity.region.sourceArc.rotated =
      (Z.cells.get (hreal.cellIndex.symm contiguity.region.source)).relator
  /-- The pasted boundary cycle has value one. -/
  cycle_value_one : GGT.RelLetter.listVal
    (Embedded.dartWord hreal.diagram contiguity.region.boundary.cycle) = 1

/-! ## A positioned outer region gives a based contiguity -/

/-- The selected planar region yields the exact based contiguity.
The source exterior is the forward cyclic source arc; the connector names are
swapped because the planar boundary is traversed in reverse source, right,
outer, left order. -/
noncomputable def RelativeBoundaryContiguity.of_embeddedData
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {R : ℕ} (Z : RelativeReducedDiagram D W R)
    (hreal : RelativeDiscRealization D W Z)
    {i : Fin hreal.diagram.rCellCount}
    (C : EmbeddedBoundaryContiguity D eps hreal.diagram i)
    (data : EmbeddedBoundaryCertificateData Z hreal C) :
    RelativeBoundaryContiguity D eps Z.boundaryWord
      (Embedded.dartWord hreal.diagram C.region.sourceArc.rotated) := by
  let sourceArc := C.region.sourceArc
  let remainder := Classical.choose
    (exists_dartWord_suffix_for_arc sourceArc)
  have hsource : Embedded.dartWord hreal.diagram sourceArc.rotated =
      Embedded.dartWord hreal.diagram sourceArc.darts ++ remainder :=
    Classical.choose_spec (exists_dartWord_suffix_for_arc sourceArc)
  have hsourceValue := arcs_value_of_cycle_value_one C.region
    data.cycle_value_one
  have htarget : C.region.target = none := C.target_eq
  have htargetBoundary :=
    targetBoundaryDarts_eq_darts_for_none C.region.targetArc htarget
  rw [htargetBoundary] at hsourceValue
  have hsourceValue' : GGT.RelLetter.listVal
      (Embedded.dartWord hreal.diagram sourceArc.darts) =
      GGT.RelLetter.listVal
        (Embedded.dartWord hreal.diagram C.region.rightSide) *
      data.position.boundaryArc.prod *
      GGT.RelLetter.listVal
        (Embedded.dartWord hreal.diagram C.region.leftSide) := by
    rw [← data.position.outer_value] at hsourceValue
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
    leftSide_short := by
      simpa only [Embedded.dartWord, List.length_map] using
        C.region.rightSide_length_le
    rightSide_short := by
      simpa only [Embedded.dartWord, List.length_map] using
        C.region.leftSide_length_le
    exterior_value := hsourceValue' }
  exact B0

/-- The positioned embedded data are inhabited at the relative interface. -/
theorem RelativeBoundaryContiguity.of_embeddedData_exists
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {R : ℕ} (Z : RelativeReducedDiagram D W R)
    (hreal : RelativeDiscRealization D W Z)
    {i : Fin hreal.diagram.rCellCount}
    (C : EmbeddedBoundaryContiguity D eps hreal.diagram i)
    (data : EmbeddedBoundaryCertificateData Z hreal C) :
    Nonempty (RelativeBoundaryContiguity D eps Z.boundaryWord
      (Embedded.dartWord hreal.diagram C.region.sourceArc.rotated)) :=
  ⟨RelativeBoundaryContiguity.of_embeddedData Z hreal C data⟩

/-- The vk package exposes the exact algebraic label associated to its
positioned planar source arc. -/
theorem EmbeddedBoundaryCertificateData.cellLabel_eq
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {D : GGT.RelGenSet G Lambda} {R : ℕ}
    (Z : RelativeReducedDiagram D W R)
    (hreal : RelativeDiscRealization D W Z)
    {eps : ℕ} {i : Fin hreal.diagram.rCellCount}
    (C : EmbeddedBoundaryContiguity D eps hreal.diagram i)
    (data : EmbeddedBoundaryCertificateData Z hreal C) :
    Embedded.dartWord hreal.diagram C.region.sourceArc.rotated =
      (Z.cells.get (hreal.cellIndex.symm i)).relator :=
  simpa only [C.source_eq] using data.cell_label_transport

end HullSC
end GroupApproximation
