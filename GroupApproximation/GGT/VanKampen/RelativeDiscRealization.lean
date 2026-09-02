import GroupApproximation.GGT.VanKampen.CactusRealization
import GroupApproximation.GGT.HullSCRelativeGreendlingerStatement

/-!
# Relative disc realizations

This file states the generic realization object for a
`HullSC.RelativeReducedDiagram`.  It includes an equivalence between the
algebraic cells and the relator cells of a planar diagram, equality of every
cell word, equality of the outer word, and diagram reducedness.

For the reduced diagrams coming from Hull's oriented least-area construction,
the explicit cactus proves all four fields.  The generic structure currently
allows an empty relator word.  Such a word cannot label a relator face because
`FaceBoundary.nonempty` forces every face word to be nonempty; the obstruction
is proved below.  Thus the unrestricted generic statement requires either a
nonempty-relator field on `RelativeReducedDiagram` or a weaker cell interface.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open GroupApproximation.HullSC

universe u w

/-- A planar realization of a common relative reduced diagram, with its
algebraic and planar relator cells identified in order. -/
structure RelativeDiscRealization
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda))) {R : ℕ}
    (Z : RelativeReducedDiagram D W R) where
  diagram : DiscDiagram.{u, w, 0} W
  cellIndex : Fin Z.cells.length ≃ Fin diagram.rCellCount
  cellWord_eq : ∀ i : Fin Z.cells.length,
    (diagram.relatorCells.get (cellIndex i)).word = (Z.cells.get i).relator
  outerWord_eq : diagram.boundaryWord =
    Z.boundaryWord.map
      (GGT.RelLetter.base : G → GGT.RelLetter G Lambda)
  reduced : diagram.Reduced

/-- The unrestricted generic realization statement.  The obstruction theorem
below identifies the missing nonempty-relator premise in the current
`RelativeReducedDiagram` interface. -/
def RelativeDiscRealizationStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda))) (R : ℕ)
    (Z : RelativeReducedDiagram D W R),
    Nonempty (RelativeDiscRealization D W Z)

namespace RelativeDiscRealization

/-- Every algebraic cell represented by a planar relator face has a nonempty
relator word. -/
theorem cellRelator_ne_nil
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    {Z : RelativeReducedDiagram D W R}
    (C : RelativeDiscRealization D W Z) (i : Fin Z.cells.length) :
    (Z.cells.get i).relator ≠ [] := by
  intro hnil
  let cell := C.diagram.relatorCells.get (C.cellIndex i)
  have hmem : cell ∈ C.diagram.relatorCells :=
    List.get_mem C.diagram.relatorCells (C.cellIndex i)
  have hword := C.diagram.relatorCell_word cell hmem
  have hstored : cell.word = [] := (C.cellWord_eq i).trans hnil
  rw [hstored] at hword
  have hlength := congrArg List.length hword
  simp only [List.length_nil, List.length_map] at hlength
  have hdarts : (C.diagram.faceBoundary cell.face).darts = [] :=
    List.length_eq_zero_iff.mp hlength.symm
  exact (C.diagram.faceBoundary cell.face).nonempty hdarts

/-- An algebraic diagram containing an empty relator cell has no realization
with a one-to-one planar relator-cell correspondence. -/
theorem not_nonempty_of_empty_cell
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    {Z : RelativeReducedDiagram D W R}
    (i : Fin Z.cells.length) (hi : (Z.cells.get i).relator = []) :
    ¬ Nonempty (RelativeDiscRealization D W Z) := by
  rintro ⟨C⟩
  exact C.cellRelator_ne_nil i hi

end RelativeDiscRealization

end VanKampen
end GGT

namespace HullSC
namespace Lemma44OrientedRelatorDiagram

open GGT.VanKampen

/-- The cell indices of an oriented algebraic diagram and its cactus relator
cells are canonically equivalent by their common finite index. -/
def cactusCellIndexEquiv
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Fin Z.cells.length ≃ Fin Z.cactusDiscDiagram.rCellCount where
  toFun i := ⟨i, by
    change i.val < Z.cactusRelatorCells.length
    rw [HullSC.Lemma44OrientedRelatorDiagram.cactusRelatorCells,
      List.length_ofFn]
    exact i.isLt⟩
  invFun j := ⟨j, by
    have hj : j.val < Z.cactusRelatorCells.length := j.isLt
    rw [HullSC.Lemma44OrientedRelatorDiagram.cactusRelatorCells,
      List.length_ofFn] at hj
    exact hj⟩
  left_inv i := by apply Fin.ext; rfl
  right_inv j := by apply Fin.ext; rfl

/-- The cactus cell at the canonical index has the corresponding algebraic
relator word. -/
theorem cactusCellIndexEquiv_word
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) :
    (Z.cactusDiscDiagram.relatorCells.get
      (Z.cactusCellIndexEquiv i)).word = (Z.cells.get i).relator := by
  change (Z.cactusRelatorCells.get (Z.cactusCellIndexEquiv i)).word = _
  rw [HullSC.Lemma44OrientedRelatorDiagram.cactusRelatorCells,
    List.get_ofFn]
  change (Z.cellAt _).relator = (Z.cellAt i).relator
  apply congrArg HullSC.Lemma44OrientedRelatorCell.relator
  apply congrArg Z.cellAt
  apply Fin.ext
  rfl

/-- The cactus realizes the common relative reduced diagram obtained from an
oriented least-area Hull diagram. -/
noncomputable def relativeDiscRealization
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram D.alphabet W R) :
    RelativeDiscRealization D W (Z.toRelativeReducedDiagram D) where
  diagram := Z.cactusDiscDiagram
  cellIndex := Z.cactusCellIndexEquiv
  cellWord_eq := Z.cactusCellIndexEquiv_word
  outerWord_eq := Z.cactusDiscDiagram_boundaryWord
  reduced := Z.cactusRealization.reduced

end Lemma44OrientedRelatorDiagram
end HullSC

namespace GGT
namespace VanKampen

/-- Every common relative diagram produced by Hull's oriented least-area
construction has the required planar realization. -/
theorem relativeDiscRealization_of_oriented
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram D.alphabet W R) :
    Nonempty (RelativeDiscRealization D W (Z.toRelativeReducedDiagram D)) :=
  ⟨Z.relativeDiscRealization D⟩

end VanKampen
end GGT
end GroupApproximation
