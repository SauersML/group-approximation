import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindClause
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceChooseLoop
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'` off the loop pockets

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-59.

Route.  Two discharges of `extremalGFaceProve_Statement` are combined by cases on the pocket.
When a single simple closed stretch of the walk gives a valid face set (`gfaceChoose_Loop K`,
`Piece10Live/GFaceChooseLoop`), `gfaceChoose_of_loop` gives the face-set clauses outright.
Otherwise a winding choice with walk-discharged clauses 4, 8 and 9
(`gfaceWindClause_Choice K`, `Piece10Live/GFaceWindClause`) gives them through
`gfaceWindClause_choice` and `gfaceWind_of_choice`.  So the winding choice is only needed on
pockets with no loop choice.

* `gfaceWindFive_Statement` (OPEN): `gfaceWindClause_Statement` with the extra premise
  `¬ gfaceChoose_Loop K`.
* `gfaceWindFive_extremal` (proved): it implies `extremalGFaceProve_Statement`.
* `gfaceWindFive_of_clause`, `gfaceWindFive_of_wind` (proved): it follows from
  `gfaceWindClause_Statement` and from `gfaceWind_Statement`.

**LOUD: logical status.**  In Lean the residual sits strictly between the two proved
directions: `gfaceWind_Statement ⇒ gfaceWindFive_Statement ⇒ extremalGFaceProve_Statement`.
The converse `gfaceWindFive_Statement ⇒ gfaceWind_Statement` is NOT proved and not available:
on a loop pocket of keep type (`F' = sideFaces A`) no winding choice is constructed (reaching
`c = A` would need peeling `q ++ p` into simple closed stretches).  It is therefore NOT an
equivalent restatement of `gfaceWind_Statement`; it drops every loop pocket, about 99% of the
model decompositions.  It is not claimed strictly weaker in truth value: gl-p10-55 argues that
`gfaceWind_Statement` and `extremalGFaceProve_Statement` are mathematically equivalent, and
this residual lies between them.  Clause 5 and part (d) are not closed here; the existence of a
nonempty excision sequence is proved separately (`gfaceWindFive_reach`,
`Piece10Live/GFaceWindFiveStep`).  **LOUD: on the no-loop pockets `SrcOut` never held in the
model** (below), so the residual effectively needs clause 4 from the walk regions, not from
`SrcOut`.

## Truth check

Scratchpad `gl-p10-59/five.py`, on the Lean-faithful models of `gl-p10-49/gface.py`,
`gl-p10-52/loop.py` (loop choice in the Lean form `C = p ++ A ++ q`, some face in `F'`) and the
integer reach of `gl-p10-55/wind.py` (`KEPT=exists`).  Random maps seeds 1 and 3 and witness maps
seed 2, 150 s each: 24163679 decompositions, 164925 with no loop choice; on all of them a
reached `0/1` state satisfies the face-set clauses (so `gfaceWindClause_Choice` holds):
0 failures.  `SrcOut` held on 0 of the 164925.  The searches do not model least area, labels
or `G`-faces.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

/-- **The winding flip statement off the loop pockets** (OPEN; see the module docstring for its
logical status).  Under the premises of `extremalGFaceProve_Statement` and when no loop choice
exists, a winding choice of `F'` with walk-discharged clauses 4, 8 and 9 exists. -/
def gfaceWindFive_Statement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K → ¬ gfaceChoose_Loop K →
        gfaceWindClause_Choice K

/-- **The face-set flip statement from the winding statement off the loop pockets**: loop
pockets by `gfaceChoose_of_loop`, the others by the winding choice. -/
theorem gfaceWindFive_extremal (h : gfaceWindFive_Statement.{u, w, v}) :
    extremalGFaceProve_Statement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  rcases Classical.em (gfaceChoose_Loop K) with hL | hL
  · exact gfaceChoose_of_loop K hK hpinch hL
  · exact gfaceWind_of_choice K hK (gfaceWindClause_choice K hK
      (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL))

/-- **The winding statement off the loop pockets from its walk-discharged form.** -/
theorem gfaceWindFive_of_clause (h : gfaceWindClause_Statement.{u, w, v}) :
    gfaceWindFive_Statement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose _
  exact h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose

/-- **The winding statement off the loop pockets from the winding flip statement.** -/
theorem gfaceWindFive_of_wind (h : gfaceWind_Statement.{u, w, v}) :
    gfaceWindFive_Statement.{u, w, v} :=
  gfaceWindFive_of_clause (gfaceWindClause_of_statement h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindFive_Statement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindFive_extremal
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindFive_of_clause
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindFive_of_wind
