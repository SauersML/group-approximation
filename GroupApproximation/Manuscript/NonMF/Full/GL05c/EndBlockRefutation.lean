import GroupApproximation.Manuscript.NonMF.Full.GL05c.EndBlockFailure
import GroupApproximation.Meta.AxiomGuard

/-!
# `ExtremalEndBlockStatement` is FALSE: one counterexample refutes it

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane nm-gl05c-01.

**Verdict: `ExtremalEndBlockStatement` (module `GL05c/Statement`) is false.**  It pins the kept
cell `K.kept` and both carrier arcs `K.sourceArc`, `K.targetArc` of the given pocket, and asks for
one face class whose move keeps `K.kept` and meets both arcs in end blocks.  The 16-dart model in
the docstring of `GL05c/Statement` has no such class.

## The model

* Vertices `w`, `u`, `z`.  Loops `p`, `e` at `w`, `q1` at `u`, `q2` at `z`.  Double edges
  `R1a, R1b` between `w` and `u` and `R2a, R2b` between `w` and `z`.
* Faces `P = [p]`, `Q1 = [q1]`, `Q2 = [q2]`, `R1 = [R1a, R1b]`, `R2 = [R2a, R2b]`, the source cell
  `S = [αR2b, αq2, αR2a, e2]` and the exterior `O = [αp, αR1b, αq1, αR1a, e1]`.
  `V - E + F = 3 - 8 + 7 = 2`.
* `K.faces = {P, R1, Q1, R2, Q2}`, `K.kept = P`, `K.source = S`, `eps = 1`.
* The cycle is `[] ++ [R2a, q2, R2b] ++ [p] ++ [R1a, q1, R1b]`, so `t₁⁻¹ = [R2a, q2, R2b]` and
  `t₂ = [R1a, q1, R1b]` (`start 1`, `length 3` in `outerDarts = [e2, R1a, q1, R1b, p]`).
* Its first turns fail only at `w`, and there the three passages pairwise cross, so
  `AllNonFirstTurnsCrossed` holds and `FirstTurns` fails.  `¬Unpinched`: the boundary darts
  `R2a`, `p`, `R1a` all start at `w`.
* Labels (group `Multiplicative ℤ`, one generator family equal to `⊤`, so every label is a
  letter).  Either all six inner faces are relator cells of value `1`
  (`p = q1 = q2 = 1`, `R1a = R2a = 2`, `R1b = R2b = -1`, `e1 = -3`, boundary value `6`, so area
  `6` is least), or only `P` and `S` are relator cells (`q1 = q2 = 0`, `R1a + R1b = 0`,
  `R2a + R2b = 0`, `e1 = -1`, boundary value `2`, area `2` least).

The face classes are `O ∪ S`, `P`, `R1`, `Q1`, `R2`, `Q2`.  Every one fails a conjunct of
`ExtremalEndBlockConclusion`, in exactly the four ways of `GL05c/EndBlockFailure`:
* `O ∪ S` meets the exterior (`endBlock_not_conclusion_of_outer`);
* `P` contains the kept cell (`endBlock_not_conclusion_of_kept`);
* `R1` colours `t₂` as `false, true, false` and `Q1` as `true, false, true`
  (`endBlock_not_isEndBlock_middle`, `endBlock_not_isEndBlock_ends`,
  `endBlock_not_conclusion_of_targetArc`);
* `R2` and `Q2` do the same on `t₁⁻¹` (`endBlock_not_conclusion_of_invSourceArc`).
These counts were checked by a script on the explicit permutations (lane scratch `check.py`).

## Relation to the GreendlingerLeaf residual

`P10RoseExtremalTrim.RoseExtremalJunctionStatement` (still open) has the same hypotheses but an
existential conclusion: some kept cell, fresh arcs `t₁`, `t₂` and sides `s₁`, `s₂` with walk
junctions.  The model does **not** refute it.  In the first labelling take `r = p` with kept cell
`R1`.  In the second take the class `Q1` with `s₁ = [R1b]`, `t₁⁻¹ = [R2a, q2, R2b]`,
`s₂ = [p]`, `t₂ = [R1a]`.  Neither statement implies the other.  The fresh-arc form is the correct
one, and item 1 of Part (b) of `P10RoseExtremalTrim/Reduction` should be read with fresh arcs.
The proved corrected forms of the pinned-arc statement are `extremalEndBlock_of_lake` and
`extremalEndBlock_of_region` in `GL05c/Statement`.

## What is proved here, and the gap

* `endBlock_not_statement_of_counterexample`: any pocket that satisfies the hypotheses of
  `ExtremalEndBlockStatement` while every dart fails the conclusion refutes the statement.
* `endBlock_not_statement_of_classes`: the same, when every dart fails in one of the four ways of
  `GL05c/EndBlockFailure`.

The remaining gap for a closed `¬ExtremalEndBlockStatement` is building the model above as a
`DiscDiagram`: planarity, the seven face boundaries, the boundary cycle, least area, and the
computation of the six face classes.

## Manuscript status

Infrastructure for `thm:hull` (`non_mf_groups_exist.tex`, tex 2121, through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL05c

universe u w v

open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

/-- **A counterexample refutes `ExtremalEndBlockStatement`**: a pocket satisfying every
hypothesis of the statement in which no dart satisfies `ExtremalEndBlockConclusion`. -/
theorem endBlock_not_statement_of_counterexample {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))} (D : GGT.RelGenSet G Lambda) (eps : ℕ)
    (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ) (hlea : X.LeastArea)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (hnft : ¬GroupApproximation.Full.GL05c.FirstTurns K)
    (hsrc : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length)
    (hpinch : ¬GroupApproximation.Full.GL05c.Unpinched X.toCombMap K.faces)
    (hrose : GroupApproximation.Full.GL05c.AllNonFirstTurnsCrossed K)
    (hfail : ∀ r : X.toCombMap.Dart, ¬ExtremalEndBlockConclusion K r) :
    ¬ExtremalEndBlockStatement.{u, w, v} := by
  intro h
  obtain ⟨r, hr⟩ := h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact hfail r hr

/-- **A counterexample by the four failures refutes `ExtremalEndBlockStatement`**: every dart's
class meets the exterior, or meets the kept cell, or leaves no end block on `t₂` or on `t₁⁻¹`. -/
theorem endBlock_not_statement_of_classes {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))} (D : GGT.RelGenSet G Lambda) (eps : ℕ)
    (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ) (hlea : X.LeastArea)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (hnft : ¬GroupApproximation.Full.GL05c.FirstTurns K)
    (hsrc : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length)
    (hpinch : ¬GroupApproximation.Full.GL05c.Unpinched X.toCombMap K.faces)
    (hrose : GroupApproximation.Full.GL05c.AllNonFirstTurnsCrossed K)
    (hcases : ∀ r : X.toCombMap.Dart,
      (∃ x, X.toCombMap.faceOf x = X.outerFace ∧ Relation.EqvGen (CombMap.FaceClassStep
        X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∨
      (∃ x, X.toCombMap.faceOf x = (cell X K.kept).face ∧ Relation.EqvGen (CombMap.FaceClassStep
        X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∨
      ¬GL05b.IsEndBlock (GL05b.movePred X.toCombMap
        (GL05b.regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r))
        K.targetArc.darts ∨
      ¬GL05b.IsEndBlock (GL05b.movePred X.toCombMap
        (GL05b.regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r))
        (invDarts X K.sourceArc.darts)) :
    ¬ExtremalEndBlockStatement.{u, w, v} :=
  endBlock_not_statement_of_counterexample D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch
    hrose (endBlock_forall_not_conclusion K hcases)

end GroupApproximation.Full.GL05c

#audit_axioms GroupApproximation.Full.GL05c.endBlock_not_statement_of_counterexample
#audit_axioms GroupApproximation.Full.GL05c.endBlock_not_statement_of_classes
