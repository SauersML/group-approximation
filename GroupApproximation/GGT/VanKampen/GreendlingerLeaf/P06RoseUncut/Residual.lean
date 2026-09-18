import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06RoseUncut.Embed
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06RoseUncut.Filter
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06, uncut rose: the residual without an in-place sub-walk move

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining two cells.

Target: `Piece06.CellRoseUncutStatement` (`Piece06/RoseCut.lean:175`), OPEN.  This module does
not close it.  It proves one more case and isolates the rest as `p06RoseUncut_NoMoveStatement`.

## The reduction

`p06RoseUncut_NoMoveStatement` is `CellRoseUncutStatement` with one extra hypothesis:
`¬ p06RoseUncut_Move K`, no in-place sub-walk move (module `P06RoseUncut/Move`).  The reduction
`p06RoseUncut_cellRoseUncut_of_noMove` goes by cases on `p06RoseUncut_Move K`.  With a move,
`p06RoseUncut_exists_step_of_move` gives the step in the same diagram, with the identity
O-equivalence.  Without one, the residual applies.

## Why the residual is strictly smaller in proof content

* It is `CellRoseUncutStatement` with one more hypothesis, so it is a consequence of the target.
* The excluded case is proved (`p06RoseUncut_exists_step_of_move`).  It is not ruled out by the
  target's own hypotheses.  The target already assumes `¬ CellCut K`, which is the case of
  `Piece06.exists_step_of_cellCut'`, but it does not assume `¬ CellFilterMove K`.  A filter move
  (`Piece06.exists_step_of_cellFilterMove'`) is a move (`p06RoseUncut_move_of_cellFilterMove`,
  module `P06RoseUncut/Filter`).  So the residual drops every uncut configuration with a filter
  move.  Example: the lake model of `P10Rose/Lobe` (two lakes `H_1`, `H_2` touching `∂K` only at
  the pinch vertex `v`, with the arcs on the exterior petal).  Each lobe at `v` shares the face class
  of a lake edge with another lobe, so there is no closed cut.  Filling both lakes keeps the
  exterior petal, which is a closed walk at `v` holding both arcs, and removes the two lake petals
  at `v`: this is a filter move.
* A move may also change the two cells (`i' ≠ j'` are free in `p06RoseUncut_Move`).  Neither
  corpus step allows this.
* `¬ CellCut K` in the residual is redundant: `p06RoseUncut_not_cellCut_of_not_move` (module
  `P06RoseUncut/Embed`) derives it from `¬ p06RoseUncut_Move K`.  It is kept so that the residual
  reads as the target plus one hypothesis.

## Truth check

The residual follows from the target, so it is true if the target is.  The target has no known
refutation.  It is not on the FALSE lists of the Greendlinger frontier audit.  The false in-place
lakes variant ("no `CellFilterMove` ⇒ a step in the same diagram") is avoided: the residual keeps
the conclusion over O-equivalent copies `X'`.

Small models checked on paper:

1. *The three-petal rose* (module docstring of `Piece06/RoseCut`).  The residual must still hold
   there, and it has no move.  There are no lakes, so a face set whose boundary darts lie on `c`
   must avoid the complement of `K.faces`, which is the exterior class.  It is therefore a union
   of petals.  Its boundary carries arcs of two distinct cells only when it holds both `P_1` and
   `P_2`.  It holds a relator cell only when it also holds `P_k`.  That union is all of `K.faces`,
   so `L' = []`, and the shared-vertex clause fails.  So the residual keeps the configuration that
   needs a change of diagram, as it must.  It is not a counterexample: `OEquivalentDiscDiagram`
   fixes only the boundary word and the relator cell words, so `X'` may be redrawn.
2. *The lake model* (above).  There is a move, so the configuration leaves the residual.
3. *A simple pocket* (`Unpinched`).  It is excluded by `¬ Unpinched`, as in the target.

## Remaining gap

The residual is the rose step for pinched cell pockets in walk order that have no closed cut and no
in-place sub-walk move.  In the three-petal rose every non-first turn is crossed, and the
three-petal rose has no move.  So the step there must change the diagram.  This needs a planar
re-drawing (surgery) of the rose, and there is no such construction in the library.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/
