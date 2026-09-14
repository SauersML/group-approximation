import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedBridgeDoublingModel
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedBridgeDoublingProof
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSubdiagramSuccProof
import GroupApproximation.Meta.AxiomGuard

/-!
# The enclosed subdiagram of a walk turning to its successor, assembled

`ClosedWalkEnclosedSubdiagramSuccStatement` (`ClosedWalkEnclosedSucc`): a face set enclosed by an
outside walk turning to its successor bounds a disc diagram `Ξ` that reads the inverse walk, has at
most as many relator cells as the face set holds, at least one when it holds one, a word-preserving
embedding of its cells into the enclosed cells, and least area when `Δ` has.

* `enclosedBridgeDoublingCellsSucc : EnclosedBridgeDoublingCellsSuccStatement`: the induction on the
  number of bridge darts (`EnclosedBridgeDoubling.doublingOutputSucc`), whose output is the
  conclusion of the statement.
* `closedWalkEnclosedSubdiagramSucc : ClosedWalkEnclosedSubdiagramSuccStatement`, closed: the pocket
  diagram of the doubled, bridge-free face set (`closedWalkEnclosedSubdiagramSucc_of_doublingCells`).
* `islandModel_enclosedSubdiagramSucc` (calibration): on the island model, whose walk runs along a
  bridge, the hypothesis of the statement holds (`BridgeDoublingModel.enclosedFaceSetSucc`) and so do
  the clauses of its conclusion, realized by the diagram itself
  (`ClosedWalkIslandModel.enclosedSubdiagram_realized`).  So the statement is neither vacuous nor
  refuted on a walk with bridges.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemmas 9.4 and 9.7); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **Doubling the bridges, with the relator cells.**  The induction on the number of bridge darts,
whose output is the conclusion of the statement. -/
theorem enclosedBridgeDoublingCellsSucc : EnclosedBridgeDoublingCellsSuccStatement.{u, w, v} := by
  intro G _ Lambda W Delta faces outerWalk E
  exact EnclosedBridgeDoubling.doublingOutputSucc _ Delta faces outerWalk rfl E

/-- **The enclosed subdiagram of a walk turning to its successor**, closed. -/
theorem closedWalkEnclosedSubdiagramSucc : ClosedWalkEnclosedSubdiagramSuccStatement.{u, w, v} :=
  closedWalkEnclosedSubdiagramSucc_of_doublingCells enclosedBridgeDoublingCellsSucc

open ClosedWalkIslandModel

open scoped Classical in
/-- **Calibration on the island model.**  The exterior walk `[1,2,5,3]`, which runs along the bridge
`t` twice, encloses `{Π, I}` and turns to its successor, and the clauses of the conclusion of
`ClosedWalkEnclosedSubdiagramSuccStatement` hold there. -/
theorem islandModel_enclosedSubdiagramSucc :
    EnclosedFaceSetSucc diagram islandFaces outerWalk ∧
      ∃ Xi : DiscDiagram.{0, 0, 0} W,
        Xi.boundaryWord = Embedded.dartWord diagram (Embedded.invDarts diagram outerWalk) ∧
        Xi.rCellCount ≤ (diagram.relatorCells.filter fun C => C.face ∈ islandFaces).length ∧
        ((∃ C ∈ diagram.relatorCells, C.face ∈ islandFaces) → 0 < Xi.rCellCount) ∧
        (∃ ι : Fin Xi.rCellCount ↪ Fin diagram.rCellCount, ∀ j : Fin Xi.rCellCount,
          (Embedded.cell Xi j).word = (Embedded.cell diagram (ι j)).word ∧
            (Embedded.cell diagram (ι j)).face ∈ islandFaces) ∧
        (diagram.LeastArea → Xi.LeastArea) :=
  ⟨BridgeDoublingModel.enclosedFaceSetSucc, enclosedSubdiagram_realized⟩

end GroupApproximation.GGT.VanKampen

#audit_closed_axioms GroupApproximation.GGT.VanKampen.enclosedBridgeDoublingCellsSucc
#audit_closed_axioms GroupApproximation.GGT.VanKampen.closedWalkEnclosedSubdiagramSucc
#audit_axioms GroupApproximation.GGT.VanKampen.islandModel_enclosedSubdiagramSucc
