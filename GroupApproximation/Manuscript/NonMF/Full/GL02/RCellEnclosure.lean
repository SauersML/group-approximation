import GroupApproximation.Manuscript.NonMF.Full.GL02.RCellSpan
import GroupApproximation.Manuscript.NonMF.Full.GL02.RCellEnclosureWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04: the class pocket enclosure from the class pocket turns

*GL02 copy.*  Re-proof of the foreign module `Piece04.RCellEnclosure`
(origin/main blob `00e7882ea`), moved to namespace `Piece04.GL02` since the modules it
imports include files last changed by commits marked WIP.  Only namespaces, the imports of
copied modules, and the qualification of foreign names differ from the original.

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  This module reduces
`ClassPocketEnclosureStatement` (module `Piece04.RCellSpan`) to `ClassPocketTurnStatement`.  The
new statement is combinatorial on `∂Π` and `∂Γ` and mentions no enclosed face set.

## Setting

`Γ = P.face k` is a polygon face and `Π = cell j` a relator cell, so `Π ≠ Γ` (`face_not_cell`).  `C` is a
backwards class pair whose classes both have kind `cell j`, with no endpoint inside a gap.  The face
walk of `Γ` reads `X T Y U`, with `T`, `U` the side darts of the target and source windows
(`runWindow`).  The windows themselves, gaps included, are `q⁻¹` and `p⁻¹` (`classWindow`).

## The isolated statement `ClassPocketTurnStatement` (OPEN)

There is a rotation `q B p A` of `∂Π`, together with:

* a dart `d ∈ p` with `α d ∈ U`, and a dart `e ∈ q` with `α e ∈ T`;
* first-turn closedness (`FirstTurnClosed`) of both complement spellings `B X` and `A Y`.

*Why it is true.*

1. *Rotation.*  This is step 2 of the argument in `Piece04.RCellSpan`.  Each window contains a side
   dart (`source_long`, `target_long`, `gap_value`), and gaps are loops at pinch vertices of `∂Π`
   carrying no dart of `Γ`.  So the two windows are disjoint cyclic arcs of `∂Π`, and `∂Π` rotates to
   `q B p A`.
2. *Crossing darts.*  `runWindow` is the side darts of `classWindow`, and it is nonempty (step 1).  A
   side dart `s` of the source window is a dart of `p⁻¹ = (p.reverse).map α`, so `s = α d` with `d ∈ p`.
   Likewise for the target window.
3. *First turns inside the pieces.*  Consecutive darts of `X` are consecutive on `∂Γ`, and consecutive
   darts of `B` are consecutive on `∂Π`.  So the successor is the face permutation, reached after one
   rotation step (`FirstTurn.of_facePerm`).
4. *First turns at the junctions.*  At a side-ended junction the four darts `X.last`, `T.head`, `q.last`,
   `B.head` meet as in the side-level setting.  The turn takes one step
   (`SameCellPocketNoncrossing.firstTurn_chain_X`, `firstTurn_close_X`).  At a gap-ended junction the
   window ends at a pinch vertex `z` of `∂Π` with a gap loop `γ`.  Rotating from `α X.last` to `B.head`
   passes the corners of the loop region `R_γ`.  Their darts are darts of `γ`, their reversals, or
   interior darts of `R_γ`.  None lies on `B X`: `γ` lies on `q`, and an edge with `Π` on both sides is
   a bridge of the planar map.  A loop at `z` through such an edge returns along its reversal, so both
   darts lie on `γ`, and `B` has no dart inside `R_γ`.

## The reduction proved here

`classPocketEnclosure_of_turns` applies `RCellPocketWalk.pocketEnclosure` (module
`Piece04.RCellEnclosureWalk`).  Its hypotheses are:

* `f = Γ`, with `hf = P.face_not_cell k j`;
* `T`, `U` the run windows;
* `q`, `p` the class window arcs;
* the crossing darts and first turns of `ClassPocketTurnStatement`.

That lemma is the side-level spur enclosure `osinLemma94CaseOneSpurEnclosure`, with the crossing
darts and first turns as hypotheses.  Its steps:

* `f` and `Π` are off each enclosure;
* the two enclosures are disjoint;
* the exterior face is off one of them.

`rCell_of_classPocketTurns` then feeds `rCell_of_classPocketEnclosure`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.CaseOneWalk

/-- **The class pocket turns** (OPEN).  For a backwards class pair of one relator cell `Π`, with no
endpoint inside a gap: `∂Π` rotates to `q B p A`, each class window has a side dart reversing a dart
of its arc, and both complement spellings `B X`, `A Y` are closed by first turns. -/
def ClassPocketTurnStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k) (Q.classCount k)
      (Q.relatorClasses k) (Q.longClasses k) eps),
    C.b' < C.b → ¬ Q.GapEndpoint k C →
    ∀ (j : Fin S.diagram.rCellCount) (sourceArc targetArc : CyclicArc (cellDarts S.diagram j))
      (X Y : List S.diagram.toCombMap.Dart) (r : ℕ),
      Q.classKind k C.source = .cell j → Q.classKind k C.target = .cell j →
      (S.diagram.faceBoundary (P.face k)).darts.rotate r =
        X ++ Q.runWindow k C.target C.b' C.b ++ Y ++ Q.runWindow k C.source C.a C.a' →
      sourceArc.reverseDarts = Q.classWindow k C.source C.a C.a' →
      targetArc.reverseDarts = Q.classWindow k C.target C.b' C.b →
      ∃ (n : ℕ) (B A : List S.diagram.toCombMap.Dart),
        (cellDarts S.diagram j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A ∧
        (∃ d ∈ sourceArc.darts,
          S.diagram.toCombMap.alpha d ∈ Q.runWindow k C.source C.a C.a') ∧
        (∃ e ∈ targetArc.darts,
          S.diagram.toCombMap.alpha e ∈ Q.runWindow k C.target C.b' C.b) ∧
        FirstTurnClosed S.diagram.toCombMap (B ++ X) ∧
        FirstTurnClosed S.diagram.toCombMap (A ++ Y)

/-- **The class pocket enclosure from the class pocket turns.** -/
theorem classPocketEnclosure_of_turns (hturns : ClassPocketTurnStatement.{u, w, v}) :
    ClassPocketEnclosureStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts S P Q k C hback hnogap j sourceArc targetArc X Y r
    hks hkt htrav hsource htarget
  obtain ⟨n, B, A, hPi, ⟨d, hd, hdU⟩, ⟨e, he, heT⟩, hturn₁, hturn₂⟩ :=
    hturns Q k C hback hnogap j sourceArc targetArc X Y r hks hkt htrav hsource htarget
  exact ⟨n, B, A, hPi, fun hne₁ hne₂ =>
    RCellPocketWalk.pocketEnclosure (P.face_not_cell k j) htrav hPi hd hdU he heT hne₁ hne₂
      hturn₁ hturn₂⟩

/-- **The relator-cell branch of GapSpan from the class pocket turns.** -/
theorem rCell_of_classPocketTurns (hturns : ClassPocketTurnStatement.{u, w, v}) :
    OsinLemma94ClassCaseOneRCellStatement.{u, w, v} :=
  rCell_of_classPocketEnclosure (classPocketEnclosure_of_turns hturns)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.classPocketEnclosure_of_turns
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.rCell_of_classPocketTurns
