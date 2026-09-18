import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindThirteen
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindCell
import GroupApproximation.Meta.AxiomGuard

/-!
# The explicit lobe statements on pockets of relator cells

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-78.

`gfaceWindTwelve_Statement` and `gfaceWindThirteen_Statement` are **FALSE** on the model with
`0`-cells (they imply the false `gfaceWindNine_Statement`, see `GFaceWindCell.lean`).  Here they
get the extra hypothesis `gfaceWindCell_RCells K` (every face of `K.faces` is a relator cell).

* `gfaceWindCell_TwelveStatement`, `gfaceWindCell_ThirteenStatement` (OPEN; definitions).
  `gfaceWindCell_twelve_of_twelve`, `gfaceWindCell_thirteen_of_thirteen` (proved): **strictly
  weaker** than the false originals.
* `gfaceWindCell_thirteen_of_twelve`, `gfaceWindCell_nine_of_thirteen` (proved): the cell
  versions are ordered like the originals, Twelve ⇒ Thirteen ⇒ `gfaceWindCell_NineStatement`
  (**STRONGER** than the cell Nine statement; no converse is proved).
* `gfaceWindCell_extremal_of_thirteen` (proved): with `gfaceWindCell_CollapseStatement`, the
  cell Thirteen statement gives `extremalGFaceProve_Statement`.

## Truth check

Scratchpad `gl-p10-78/cellcheck2.py` (the lobe forms of `gl-p10-73/leanexact.py`, relator
cells `K.faces ∪ {source}`); see the lane report for the counts.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

/-- **The explicit two-lobe statement on pockets of relator cells** (OPEN; STRICTLY WEAKER than
the false `gfaceWindTwelve_Statement`). -/
def gfaceWindCell_TwelveStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K → ¬ gfaceChoose_Loop K →
      gfaceWindCell_RCells K → gfaceWindTwelve_Lobes K

/-- **The statement with nested wraps on pockets of relator cells** (OPEN; STRICTLY WEAKER than
the false `gfaceWindThirteen_Statement`). -/
def gfaceWindCell_ThirteenStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K → ¬ gfaceChoose_Loop K →
      gfaceWindCell_RCells K → gfaceWindThirteen_Lobes K

/-- **The cell two-lobe statement from the two-lobe statement** (drop the extra hypothesis). -/
theorem gfaceWindCell_twelve_of_twelve (h : gfaceWindTwelve_Statement.{u, w, v}) :
    gfaceWindCell_TwelveStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL _
  exact h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL

/-- **The cell nested-wrap statement from the nested-wrap statement** (drop the extra
hypothesis). -/
theorem gfaceWindCell_thirteen_of_thirteen (h : gfaceWindThirteen_Statement.{u, w, v}) :
    gfaceWindCell_ThirteenStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL _
  exact h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL

/-- **The cell nested-wrap statement from the cell two-lobe statement.** -/
theorem gfaceWindCell_thirteen_of_twelve (h : gfaceWindCell_TwelveStatement.{u, w, v}) :
    gfaceWindCell_ThirteenStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL hR
  exact gfaceWindThirteen_lobes_of_twelve K
    (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL hR)

/-- **The cell arc-keeping statement from the cell nested-wrap statement.** -/
theorem gfaceWindCell_nine_of_thirteen (h : gfaceWindCell_ThirteenStatement.{u, w, v}) :
    gfaceWindCell_NineStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL hR
  exact gfaceWindThirteen_arcs_of_lobes K
    (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL hR)

/-- **The face-set flip statement from the cell nested-wrap statement and the `0`-cell
residual.** -/
theorem gfaceWindCell_extremal_of_thirteen (h : gfaceWindCell_ThirteenStatement.{u, w, v})
    (hC : gfaceWindCell_CollapseStatement.{u, w, v}) :
    extremalGFaceProve_Statement.{u, w, v} :=
  gfaceWindCell_extremal_of_cell (gfaceWindCell_nine_of_thirteen h) hC

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCell_TwelveStatement
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCell_ThirteenStatement
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCell_twelve_of_twelve
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCell_thirteen_of_thirteen
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCell_thirteen_of_twelve
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCell_nine_of_thirteen
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCell_extremal_of_thirteen
