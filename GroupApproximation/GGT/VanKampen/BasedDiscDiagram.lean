import GroupApproximation.GGT.VanKampen.DiscDiagram

/-!
# Basing the conjugators of a disc diagram

`DiscDiagram` stores `RelatorCell.conjugator` as a bare group element.  Its
only laws are `relatorCell_faces_nodup`, `relatorCell_word`, `inner_face` and
`boundary_product`; nothing anywhere relates a conjugator to a dart, a path or
a basepoint.  That is why the connector transport used by
`VanKampen.CellContiguity.leftConnector_transport` cannot be derived: a
diagram carrying different conjugators with the same `boundary_product` is
still a legal `DiscDiagram`.

`BasedDiscDiagram` adds the missing structure without touching `DiscDiagram`:
each relator cell carries a *basing path*, a dart list read from the diagram's
basepoint to that cell, whose label value is the cell's conjugator.  The
convention matches `RelatorCell.value`, which conjugates the relator word by
`conjugator` on the left, so a based cell reads as "walk out along the basing
path, once around the cell, back along the basing path".
`value_eq_basePath_conj` is that reading.

## What is proved here and what is still owed

Proved: the based reading of a cell value, and that a diagram with no relator
cells is vacuously based.

Still owed, and deliberately not stated as a field: the *reading law* that a
connector path between two cells reads the transport
`(source.conjugator⁻¹ * (between.map RelatorCell.value).prod *
target.conjugator)⁻¹`, which is exactly
`CellContiguity.leftConnector_transport`.  Stating it needs a notion of which
cells a closed walk encloses, and that notion is not available: vkpeel's
`VanKampen/ClosedWalkValue.lean` records in its own docstring that "the general
form 'the value of a closed walk is the product of the conjugated values of the
faces it encloses' is not stated here, because *encloses* has no meaning
without planarity ... and the identity is false", and replaces enclosure by an
explicit `FaceAssembly`.  `FaceAssembly` is `Prop`-valued with its insertion
prefixes implicit, so the conjugators that the product form needs are hidden
and cannot be eliminated into data; a `Type`-valued variant recording the
prefixes is required before the reading law can even be written down.  Writing
a placeholder law here would be false as stated, since two connector paths
between the same two cells differ by exactly the cells they enclose.

So this module lands the basing half, which is self-contained, and leaves the
reading law to follow the `FaceAssembly` refactor.

## Superseded route

The connector transport does not in fact have to be derived from a reading
law.  `VanKampen.CellContiguity.whole_relators_ne` already concludes the
required inequality from `DiscDiagram.Reduced` together with a
`CellContiguity` certificate, whose `split` and `leftConnector_transport`
fields are exactly the two missing facts, and
`Embedded.ReducedCellPieceBridge.of_cellContiguity` converts such a
certificate into the embedded bridge.  Carrying that certificate on
`Embedded.Contiguity` therefore closes the estimating Piece construction with
no new van Kampen lemma, and this module is kept only for the basing half,
which remains the honest reading of `RelatorCell.conjugator` and is worth
having on its own.
-/

set_option linter.unusedVariables false

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u w v

/-- A disc diagram whose relator-cell conjugators are read off basing paths.
`basePath i` is a dart list from the diagram's basepoint to the `i`-th stored
relator cell, and its label value is that cell's conjugator. -/
structure BasedDiscDiagram {G : Type u} [Group G] {Lambda : Type w}
    (W : Set (List (GGT.RelLetter G Lambda)))
    extends DiscDiagram.{u, w, v} W where
  /-- The dart path from the basepoint to the `i`-th stored relator cell. -/
  basePath : Fin toDiscDiagram.relatorCells.length →
    List toDiscDiagram.toCombMap.Dart
  /-- The stored conjugator is the value read along the basing path.  The
  orientation matches `RelatorCell.value`, which conjugates on the left by
  `conjugator`. -/
  basePath_value : ∀ i,
    (toDiscDiagram.relatorCells.get i).conjugator =
      GGT.RelLetter.listVal ((basePath i).map toDiscDiagram.label)

namespace BasedDiscDiagram

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}

/-- **The based reading of a relator cell.**  A forward cell contributes the
relator word conjugated by the value of its basing path. -/
theorem value_eq_basePath_conj (Delta : BasedDiscDiagram.{u, w, v} W)
    (i : Fin Delta.toDiscDiagram.relatorCells.length)
    (hrev : (Delta.toDiscDiagram.relatorCells.get i).reversed = false) :
    (Delta.toDiscDiagram.relatorCells.get i).value =
      GGT.RelLetter.listVal
          ((Delta.basePath i).map Delta.toDiscDiagram.label) *
        GGT.RelLetter.listVal
          (Delta.toDiscDiagram.relatorCells.get i).word *
        (GGT.RelLetter.listVal
          ((Delta.basePath i).map Delta.toDiscDiagram.label))⁻¹ := by
  simp only [RelatorCell.value, hrev, Bool.false_eq_true, if_false,
    Delta.basePath_value i]

/-- The reversed reading, for completeness. -/
theorem value_eq_basePath_conj_inv (Delta : BasedDiscDiagram.{u, w, v} W)
    (i : Fin Delta.toDiscDiagram.relatorCells.length)
    (hrev : (Delta.toDiscDiagram.relatorCells.get i).reversed = true) :
    (Delta.toDiscDiagram.relatorCells.get i).value =
      GGT.RelLetter.listVal
          ((Delta.basePath i).map Delta.toDiscDiagram.label) *
        (GGT.RelLetter.listVal
          (Delta.toDiscDiagram.relatorCells.get i).word)⁻¹ *
        (GGT.RelLetter.listVal
          ((Delta.basePath i).map Delta.toDiscDiagram.label))⁻¹ := by
  simp only [RelatorCell.value, hrev, if_true, Delta.basePath_value i]

/-- A diagram whose conjugators are the label values of single darts is based
by the one-dart basing paths.  This is the shape the cactus constructions
already have: `CactusConstruction.lean` labels the stem darts
`.stemOut i` and `.stemIn i` by `GGT.RelLetter.base` of the `i`-th cell's
conjugator and its inverse, so a stem dart is exactly a basing path of
length one. -/
def ofDartConjugators (Delta : DiscDiagram.{u, w, v} W)
    (stem : Fin Delta.relatorCells.length → Delta.toCombMap.Dart)
    (hstem : ∀ i, (Delta.relatorCells.get i).conjugator =
      GGT.RelLetter.val (Delta.label (stem i))) :
    BasedDiscDiagram.{u, w, v} W where
  toDiscDiagram := Delta
  basePath := fun i => [stem i]
  basePath_value := by
    intro i
    rw [hstem i]
    simp [GGT.RelLetter.listVal]

/-! ## Model test -/

/-- A diagram with no relator cells is based, with no basing paths to supply.
This is the degenerate model of the structure. -/
def ofNoRelatorCells (Delta : DiscDiagram.{u, w, v} W)
    (h : Delta.relatorCells = []) : BasedDiscDiagram.{u, w, v} W where
  toDiscDiagram := Delta
  basePath := fun i =>
    absurd i.isLt (by
      have hlen : Delta.relatorCells.length = 0 := by simp [h]
      omega)
  basePath_value := fun i =>
    absurd i.isLt (by
      have hlen : Delta.relatorCells.length = 0 := by simp [h]
      omega)

end BasedDiscDiagram

end VanKampen
end GGT
end GroupApproximation
