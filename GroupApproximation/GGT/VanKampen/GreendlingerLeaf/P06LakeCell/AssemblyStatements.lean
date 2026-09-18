import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.AssemblyDefs
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06, case (d): the three case statements of the lakes surgery

The target is `Piece06.CellRoseLakesSurgeryBelowStatement` (Piece06/LakesSurgery.lean:128): below
the inductive bound, an uncut cell rose pocket `K` with no side cell, no short petal and no in-place
filter move gives a lake fill with one arc outside, a lake fill with two arcs outside, or the step
on an O-equivalent copy.  Each statement below keeps every hypothesis and threshold of the target and
adds one case of `P06LakeCell.Assembly.cases_core`.

* `CellRoseLakesOutsideCellStatement` (OPEN): some relator cell lies in the exterior piece `E₀`
  (`¬ AllCellsEnclosed K`).  Route (not proved here): fill the lakes of `K`, getting `F'`, whose
  outside walk reads sub-walks of `s₁, t̄₁, s₂, t̄₂` in cyclic order.  If `Π_i` or `Π_j` is off `F'`
  this is case (a) or (c) of LakesSurgery.  If both are in `F'`, the relator cell of `E₀` is off
  the filled `F'`, and the walk reads `s₁' s₂'`; this is case (b), refuted by the short-petal exit
  (`Piece06.shortPetalFree_of_below`, RoseBelow:74), or `LakeFillOneArcExit` with the empty arc.
* `CaseDLakeRelatorExitStatement` (OPEN, lane gl-p06-11): all relator cells enclosed and a lake of
  `Π_i` or of `Π_j` holds a second relator cell.  Conclusion: one of the two lake-fill exits (the
  face set `lakeOf K i ∖ {Π_i}` with its lakes filled).  Lane gl-p06-11 states the case of the lake
  of `Π_i`; the lake of `Π_j` is the same case after swapping the roles of the two cells, so the
  hypothesis here is the disjunction.
* `CellRoseLakeGOnlyBelowStatement` (OPEN, lane gl-p06-12): all relator cells enclosed and both
  lakes `G`-only.  Expected true only circularly (short-word Greendlinger at the same count).

## Truth

`CellRoseLakesOutsideCellStatement` and `CellRoseLakeGOnlyBelowStatement` add a hypothesis to the
target and keep its conclusion, so the target implies them (`outsideCell_of_surgery`,
`gOnly_of_surgery` in `P06LakeCell/Assembly`).  They hold whenever the target does.  In case (d)
the hypotheses of the target cannot all hold, by the real Lemma 9.7 at the same count
(carto-gl-p06 §2).  So the strengthened conclusion of `CaseDLakeRelatorExitStatement` is also true
there, and it is still OPEN.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.Assembly

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated

/-- **The lakes surgery with a relator cell in the exterior piece** (OPEN).  Every hypothesis of
`Piece06.CellRoseLakesSurgeryBelowStatement`, and `¬ AllCellsEnclosed K`, with the same
conclusion. -/
def CellRoseLakesOutsideCellStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              ∀ (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount), i ≠ j → X.LeastArea →
                OsinLemma97Below.{u, w, v} D lambda c mu eps W X.rCellCount →
                (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
                ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk → ¬ K.FirstTurns →
                  K.firstArc.length < (cellDarts X i).length →
                  K.secondArc.length < (cellDarts X j).length →
                  ¬Unpinched X.toCombMap K.faces → Piece06.AllNonFirstTurnsCrossed K →
                  ¬ Piece06.CellCut K → (∀ k : Fin X.rCellCount, ¬ Piece06.SideCell K k) →
                  Piece06.ShortPetalFree eps X → ¬ Piece06.CellFilterMove K →
                  ¬ AllCellsEnclosed K →
                    Piece06.LakeFillOneArcExit eps X ∨ Piece06.LakeFillTwoArcExit D eps X ∨
                    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
                      (K' : CellPocketFaceSet D eps X' i' j'),
                      Nonempty (OEquivalentDiscDiagram X X') ∧
                        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
                        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
                        K'.secondArc.length < (cellDarts X' j').length ∧
                        K'.repeatedVisits < K.repeatedVisits

/-- **Case (d) with a second relator cell in a lake gives a lake-fill exit** (OPEN; the interface
of lane gl-p06-11, for either lake).  Every hypothesis of
`Piece06.CellRoseLakesSurgeryBelowStatement`, `AllCellsEnclosed K` and `SecondLakeCell K`,
concluding one of the two lake-fill exits. -/
def CaseDLakeRelatorExitStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              ∀ (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount), i ≠ j → X.LeastArea →
                OsinLemma97Below.{u, w, v} D lambda c mu eps W X.rCellCount →
                (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
                ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk → ¬ K.FirstTurns →
                  K.firstArc.length < (cellDarts X i).length →
                  K.secondArc.length < (cellDarts X j).length →
                  ¬Unpinched X.toCombMap K.faces → Piece06.AllNonFirstTurnsCrossed K →
                  ¬ Piece06.CellCut K → (∀ k : Fin X.rCellCount, ¬ Piece06.SideCell K k) →
                  Piece06.ShortPetalFree eps X → ¬ Piece06.CellFilterMove K →
                  AllCellsEnclosed K → SecondLakeCell K →
                    Piece06.LakeFillOneArcExit eps X ∨ Piece06.LakeFillTwoArcExit D eps X

/-- **Case (d) with both lakes `G`-only** (OPEN; the interface of lane gl-p06-12).  Every hypothesis
of `Piece06.CellRoseLakesSurgeryBelowStatement`, `AllCellsEnclosed K`, `LakeGOnly K i` and
`LakeGOnly K j`, with the same conclusion. -/
def CellRoseLakeGOnlyBelowStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              ∀ (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount), i ≠ j → X.LeastArea →
                OsinLemma97Below.{u, w, v} D lambda c mu eps W X.rCellCount →
                (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
                ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk → ¬ K.FirstTurns →
                  K.firstArc.length < (cellDarts X i).length →
                  K.secondArc.length < (cellDarts X j).length →
                  ¬Unpinched X.toCombMap K.faces → Piece06.AllNonFirstTurnsCrossed K →
                  ¬ Piece06.CellCut K → (∀ k : Fin X.rCellCount, ¬ Piece06.SideCell K k) →
                  Piece06.ShortPetalFree eps X → ¬ Piece06.CellFilterMove K →
                  AllCellsEnclosed K → LakeGOnly K i → LakeGOnly K j →
                    Piece06.LakeFillOneArcExit eps X ∨ Piece06.LakeFillTwoArcExit D eps X ∨
                    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
                      (K' : CellPocketFaceSet D eps X' i' j'),
                      Nonempty (OEquivalentDiscDiagram X X') ∧
                        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
                        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
                        K'.secondArc.length < (cellDarts X' j').length ∧
                        K'.repeatedVisits < K.repeatedVisits

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.Assembly

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.Assembly.CellRoseLakesOutsideCellStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.Assembly.CaseDLakeRelatorExitStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.Assembly.CellRoseLakeGOnlyBelowStatement
