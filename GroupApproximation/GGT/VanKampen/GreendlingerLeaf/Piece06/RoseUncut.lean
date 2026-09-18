import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.RoseCut
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.Residual
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellPinchSectionDistinct
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06: the uncut rose step, restated under Osin's condition

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining the cells `Π_i` and `Π_j`.  The module
`Piece06/RoseCut` reduces `CellRoseStepStatement` to `CellRoseUncutStatement`, which carries no
small cancellation hypothesis at all.  This module explains why that residual has no step by the
available surgeries, and restates it one level up with the hypotheses of the consumer
`CellPocketOuterPinchStepSectionDistinctStatement`.

## The three petals are not excluded by the hypotheses of `CellRoseUncutStatement`

Take the local model of `Piece06/RoseCut`: petals `P_1`, `P_2`, `P_k` of `K.faces` meeting at one
vertex `v`, pairwise touching only at `v`, with faces off `K` in the three corners between them.
`P_1` is one G-cell carrying `t̄_1` and part of the sides, `P_2` one G-cell carrying `t̄_2` and part of
the sides, and `P_k = {kept}` is the relator cell `k`, carrying sides only.  The walk enters and
leaves `v` three times, in rotation order reversed (`i_1 → o_2, i_2 → o_3, i_3 → o_1`).

* `i ≠ j`, letter labels, both arcs proper, `¬ Unpinched` (three visits of `v`),
  `¬ FirstTurns` (the turns at `v` are not the first turns), `ClosedWalk` (the petals are closed
  walks glued at `v`) and `AllNonFirstTurnsCrossed` (each turn at `v` separates the other two
  petals) all hold.
* `LeastArea` is a property of the boundary value and the relator count of `X`; nothing local at
  `v` violates it, since a least-area van Kampen diagram may contain a cell attached along a
  cut vertex.
* `¬ CellCut K`: the classes of `FaceClassStep (walkKeep c)` are the petals, so every closed cut is
  a union of petals.  The rest carries both arcs only when the cut is `P_k`, and the rest
  `P_1 ∪ P_2` then contains no relator cell.

So the hypotheses are consistent with the configuration, and `repeatedVisits K = 2`.

## Why the available surgeries give no step

(a) *Same-diagram cuts.*  Covered by `¬ CellCut K` above; a lobe carrying fewer than both arcs is not
    a cell pocket (`firstArc_pos`, `secondArc_pos`).
(b) *Reordering the walk.*  `repeatedVisits` depends only on the face set (`RoseCut`, point 1).
(c) *The pinch split* (`CellPocketFaceSet.pinchSplit`, `PinchSplit.Input`).  It needs two corner
    faces at `v` that are distinct, not the exterior face and not relator cells.  The corners
    between the petals are faces off `K`: the exterior face, or the cells `i`, `j` across `t_1`,
    `t_2`, are admissible values, and then no input exists.
(d) *Moving the kept cell.*  `P_1 ∪ P_2` holds no relator cell, and deleting or merging the cell
    `k` changes `rCellCount`, which `OEquivalentDiscDiagram` forbids (a bijection of cell indices).
(e) *The first-turn normal form* (`exists_simple_of_firstTurns`) needs `FirstTurns`, which fails.

This does not refute `CellRoseUncutStatement`: its conclusion allows any O-equivalent copy and any
pair of cells, and no argument above shows that no copy has a cell pocket with fewer repeated
visits.  But no proof of the residual can be a local surgery at `v`.

## What excludes the configuration in the paper

In the model the whole boundary cycle of the kept cell lies on the sides, so its relator word has
length at most `|s_1| + |s_2| ≤ 2ε`.  Under `OsinCCondition D W ε μ λ c ρ`, every word of `W` has
length at least `ρ` (field `long`), so the configuration is impossible once `ρ > 2ε`.  Osin chooses
`ρ ≫ ε` exactly for this (Greendlinger's lemma for the subdiagram `Γ_1`).  More generally, a relator
cell of `Γ_1` meeting `∂Γ_1` only along the sides has perimeter at most `2ε`, contradicting the
C-condition.  The unconditional residual drops this hypothesis.

## The corrected residual

* `CellRoseUncutOsinStatement` (OPEN): `CellRoseUncutStatement` under the binders of
  `CellPocketOuterPinchStepSectionDistinctStatement`: hyperbolicity, `λ, c, μ` in range,
  thresholds `ε₀`, `ρ₀`, and `OsinCCondition D W ε μ λ c ρ`.
* `cellRoseUncutOsin_of_uncut`: the unconditional residual implies it (`ε₀ = 0`, `ρ₀ = 1`), so it
  is weaker.
* `proof_of_cellRoseUncutOsin`: it and `BadCornerRefinementStatement` give
  `CellPocketOuterPinchStepSectionDistinctStatement`, by the dispatch of `Piece06/Proof`: a closed
  cut performs the rose step in the same diagram (`exists_step_of_cellCut'`), an uncut rose uses
  the residual, and an uncrossed turn uses the good or bad corners.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated
open scoped Classical

/-- **The rose step of the cell pinch without a closed cut, under Osin's condition** (OPEN; the
residual of gap 6).  `CellRoseUncutStatement` under the binders of
`CellPocketOuterPinchStepSectionDistinctStatement`: beyond thresholds for `ε` and `ρ`, for a family
satisfying Osin's condition.  The condition excludes the three petals of the module docstring. -/
def CellRoseUncutOsinStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              ∀ (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount), i ≠ j → X.LeastArea →
                (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
                ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk → ¬ K.FirstTurns →
                  K.firstArc.length < (cellDarts X i).length →
                  K.secondArc.length < (cellDarts X j).length →
                  ¬Unpinched X.toCombMap K.faces → AllNonFirstTurnsCrossed K → ¬ CellCut K →
                    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
                      (K' : CellPocketFaceSet D eps X' i' j'),
                      Nonempty (OEquivalentDiscDiagram X X') ∧
                        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
                        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
                        K'.secondArc.length < (cellDarts X' j').length ∧
                        K'.repeatedVisits < K.repeatedVisits

/-- **The unconditional uncut residual implies the one under Osin's condition**: the thresholds
play no role. -/
theorem cellRoseUncutOsin_of_uncut (h : CellRoseUncutStatement.{u, w, v}) :
    CellRoseUncutOsinStatement.{u, w, v} := by
  intro G _ Lambda D _ _ _ _ _ _ _ _ _
  exact ⟨0, fun eps _ => ⟨1, Nat.one_pos, fun _ _ _ _ X i j hij hlea hlabel K hK hnft hfirst
    hsecond hpinch hrose hcut => h D eps X i j hij hlea hlabel K hK hnft hfirst hsecond hpinch
      hrose hcut⟩⟩

/-- **Piece 06 of the Greendlinger leaf from the uncut residual under Osin's condition**: a closed
cut performs the rose step in the same diagram, an uncut rose uses `CellRoseUncutOsinStatement`, and
an uncrossed turn uses the good corners or `BadCornerRefinementStatement` (OPEN, gap 5). -/
theorem proof_of_cellRoseUncutOsin (h : CellRoseUncutOsinStatement.{u, w, v})
    (hcorner : BadCornerRefinementStatement.{u, w, v}) :
    CellPocketOuterPinchStepSectionDistinctStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  refine ⟨rho0, hrho0, fun rho hrho' W hcondition X i j hij hlea hlabel K hK hnft hfirst hsecond
    hpinch => ?_⟩
  by_cases hrose : AllNonFirstTurnsCrossed K
  · by_cases hcut : CellCut K
    · exact exists_step_of_cellCut' hlabel K hK hij hfirst hsecond hcut
    · exact hrho rho hrho' W hcondition X i j hij hlea hlabel K hK hnft hfirst hsecond hpinch
        hrose hcut
  · obtain ⟨d₀, hd₀, hnf, hnc⟩ := exists_uncrossed_of_not_allCrossed hrose
    by_cases hgood : GoodTurnCorners X d₀ (K.boundary.cycle.next d₀ hd₀)
    · exact exists_step_of_goodCorners hlabel K hK hij hfirst hsecond hd₀ rfl hnf
        (huncross_of_not_turnCrossed hnc) hgood
    · exact exists_step_of_badCorners hcorner hlabel K hK hij hfirst hsecond hd₀ rfl hnf
        (huncross_of_not_turnCrossed hnc) hgood

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CellRoseUncutOsinStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.cellRoseUncutOsin_of_uncut
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.proof_of_cellRoseUncutOsin
