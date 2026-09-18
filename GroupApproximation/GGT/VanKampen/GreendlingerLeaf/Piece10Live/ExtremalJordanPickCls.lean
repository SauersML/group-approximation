import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickClsPremises
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickClsClasses
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordan
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalClass
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCells
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickRun
import GroupApproximation.Meta.AxiomGuard

/-!
# LOUDLY FALSE: `ExtremalJordanStatement` and the cells hypothesis

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-40.

The G-face model of lane gl-p10-37 is realized under every premise of `ExtremalJordanStatement`.
The pocket is `ExtremalJordanPickClsModel.pK` on a disc diagram over `Perm (Fin 3)` with sixteen
darts and relator cells `S = [7,5,3,14,1]` and `K₀ = [0]`
(`ExtremalJordanPickClsMap`, `ExtremalJordanPickClsDiagram`).  The premises are checked in
`ExtremalJordanPickClsPremises`, and the walk classes in `ExtremalJordanPickClsClasses`.

* `extremalJordanPickCls_notRose`: `RoseExtremalClassStatement.{0,0,0}` is FALSE.
* `extremalJordanPickCls_notJordan`: `ExtremalJordanStatement.{0,0,0}` is FALSE.
* `extremalJordanPickCls_notPickRun`: `ExtremalJordanPickRunStatement.{0,0,0}` is FALSE.
* `extremalJordanPickCls_notCells`: the cells hypothesis `extremalJordanPickCls_CellsHyp` of
  `extremalJordanPickCells_run_of_cellsRun` is FALSE.  The walk class `{2,6}` of the walk dart `2`
  holds no relator cell.

## Manuscript status

Counterexample to infrastructure of `thm:hull`.  It refutes no printed sentence.  It shows that
the Piece 10 route through `ExtremalJordanStatement` cannot close as stated.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf

universe u w v

open Embedded Surgery.MapCollapse

/-- **LOUDLY FALSE: `RoseExtremalClassStatement`.**  In the pocket `pK`, no dart spans a class
with `ExtremalClassChoice` and `ExtremalClassStretches`. -/
theorem extremalJordanPickCls_notRose :
    ¬P10ExtremalRegion.RoseExtremalClassStatement.{0, 0, 0} := by
  intro h
  obtain ⟨r, hch, hst⟩ := h OsinPocketPinchedTwoGonModel.D 1
    ExtremalJordanPickClsModel.diagram 0 4 ExtremalJordanPickClsModel.hwrap
    ExtremalJordanPickClsModel.leastArea ExtremalJordanPickClsModel.letters
    ExtremalJordanPickClsModel.pK ExtremalJordanPickClsModel.closedWalk
    ExtremalJordanPickClsModel.notFirstTurns ExtremalJordanPickClsModel.srcLt
    ExtremalJordanPickClsModel.tgtLt ExtremalJordanPickClsModel.notUnpinched
    ExtremalJordanPickClsModel.allCrossed
  exact ExtremalJordanPickClsModel.no_class r hch hst

/-- **LOUDLY FALSE: `ExtremalJordanStatement`.** -/
theorem extremalJordanPickCls_notJordan :
    ¬P10ExtremalRegion.ExtremalJordanStatement.{0, 0, 0} := fun h =>
  extremalJordanPickCls_notRose (P10ExtremalRegion.roseExtremalClass_of_extremalJordan h)

/-- **LOUDLY FALSE: `ExtremalJordanPickRunStatement`.** -/
theorem extremalJordanPickCls_notPickRun :
    ¬P10ExtremalRegion.ExtremalJordanPickRunStatement.{0, 0, 0} := fun h =>
  extremalJordanPickCls_notJordan (P10ExtremalRegion.extremalJordanPickRun_extremalJordan h)

/-- **The cells hypothesis** `hcls` of `extremalJordanPickCells_run_of_cellsRun`: under the
premises of `ExtremalJordanStatement`, every walk class holds a relator cell.  LOUDLY FALSE
(`extremalJordanPickCls_notCells`). -/
def extremalJordanPickCls_CellsHyp : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K → P10ExtremalRegion.ExtremalJordanPickCellsClass K

/-- **LOUDLY FALSE: the cells hypothesis.**  The walk class `{2,6}` of the walk dart `2` of `pK`
holds no relator cell. -/
theorem extremalJordanPickCls_notCells : ¬extremalJordanPickCls_CellsHyp.{0, 0, 0} := fun h =>
  ExtremalJordanPickClsModel.class_two (h OsinPocketPinchedTwoGonModel.D 1
    ExtremalJordanPickClsModel.diagram 0 4 ExtremalJordanPickClsModel.hwrap
    ExtremalJordanPickClsModel.leastArea ExtremalJordanPickClsModel.letters
    ExtremalJordanPickClsModel.pK ExtremalJordanPickClsModel.closedWalk
    ExtremalJordanPickClsModel.notFirstTurns ExtremalJordanPickClsModel.srcLt
    ExtremalJordanPickClsModel.tgtLt ExtremalJordanPickClsModel.notUnpinched
    ExtremalJordanPickClsModel.allCrossed)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.extremalJordanPickCls_notRose
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.extremalJordanPickCls_notJordan
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.extremalJordanPickCls_notPickRun
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.extremalJordanPickCls_CellsHyp
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.extremalJordanPickCls_notCells
