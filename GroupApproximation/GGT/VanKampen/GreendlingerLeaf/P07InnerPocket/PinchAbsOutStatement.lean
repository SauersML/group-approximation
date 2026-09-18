import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsSubStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsOutFollow
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-74: the outside statement is FALSE; corrected residual

**LOUD: `pinchAbsSub_OutsideStatement` (`PinchAbsSubStatement.lean:57`) is FALSE.**
Counterexample (scratch `gl-p07-74/counter.py`, checked with the Lean conventions of
`gl-p07-74/cmap.py`): the plane graph with vertices `v (0,0)`, `x (2,2)`, `y (-2,2)`, `p (0.3,1)`,
`q (-0.3,1)` and edges `vx, xy, yv, vp, pq, qv` (an inner triangle `vpq` hanging at `v` inside the
triangle `vxy`).  It has 3 faces: the exterior, the triangle `vpq`, and the face `f` between them,
whose boundary walk (darts `[1,6,8,10,5,3]`) passes through `v` twice.  Take `walk` = this face
cycle of `f` and the exterior as `outerFace` (trivial group, any labels: a disc diagram).  Then
`walk` is a noncrossing closed walk, `sideFaces walk = {f}`, the outer face is off the side, and
both reclosed maps have Euler characteristic `2 = χ`.  But the two faces off the side (exterior
and `vpq`) meet only at `v`: they share no edge, so `pinchAbsSub_Outside` fails.

*Why the Euler equalities cannot see it.*  Write `χ_c(S) = V_int(S) - E_int(S) + |S|` for the
side `S` and likewise for the outside `O`.  Reclosing `S` keeps the rotation at the walk vertices,
so the inner equality says `χ_c(S) = 1`.  Reclosing `O` splits a vertex visited `k` times into
`k` vertices, so the outer equality says `χ_c(O) = 1 + (|w| - V_w)`.  Globally
`2 = χ_c(S) + χ_c(O) + V_w - |w|`, so the OUTER EQUALITY FOLLOWS FROM THE INNER ONE.  An outside
made of two discs touching at a twice visited vertex has `χ_c(O) = 2 = 1 + 1`.  (The ring of
gl-p07-73, a pinched SIDE, violates the inner equality; a pinched OUTSIDE violates neither.)

**The correct extra premise is `(hw.outerCycle X.planar).FollowsBoundary`**, and then no Euler
hypothesis is needed: `pinchAbsOut_outside_of_follows` (`PinchAbsOutFollow.lean`) proves
`pinchAbsSub_Outside` outright, and `pinchAbsOut_outsideStatement` packages it as the corrected,
pocket-free `pinchAbsOut_OutsideStatement`.

**Truth check** (scratch `gl-p07-74/follow_check.py`, seeds 1, 2, 3, 400 random perturbed grid
maps each, walks traced from random face sets): 12464 noncrossing closed walks, all with both
Euler equalities.  `OUT ⇔ FollowsBoundary` held in all 12464 (11088 with both, 1376 with
neither), so 1376 further counterexamples to `pinchAbsSub_OutsideStatement`, and no walk with
`FollowsBoundary` and a disconnected outside (as `pinchAbsOut_outside_of_follows` predicts).

**LOUD: consequence for the chain.**  The pinched configuration upstream is exactly the case
`¬ FollowsBoundary` (`InnerPocketEnclosedTwoArcPinchedCorrected`,
`Manuscript/NonMF/Full/GL03BPinch/Statement.lean:131`).  In every sampled walk with
`¬ FollowsBoundary` the outside was disconnected, so `pinchAbsSub_Rest` (which contains `OUT`) is
expected to be FALSE throughout the pinched case: the `OUT` route of gl-p07-73 only covers the
case where the outer cycle follows its boundary.  The corrected residual below keeps that route
for that case (where `OUT` is now proved) and asks `pinchAbs_Cut` directly otherwise.

* `pinchAbsOut_Rest hw`: `FollowsBoundary → pinchAbsSub_TouchTail` and
  `¬ FollowsBoundary → pinchAbs_Cut`.
* `pinchAbsOut_cut_of_rest`: `pinchAbsOut_Rest → pinchAbs_Cut` (given `f ∈ side K`).
* `pinchAbsOut_ResidualStatement`: the premise block of `pinchAbsSub_ResidualStatement` verbatim,
  with the conclusion `pinchFollow_Conclusion ∨ pinchAbsOut_Rest`.
* `pinchAbsOut_of_statement`: the `_of_` reduction to `pinchAbs_ResidualStatement`.
* `pinchAbsOut_statement_of_sub`: `pinchAbsSub_ResidualStatement → pinchAbsOut_ResidualStatement`.

**LOUD: logical strength.**  As Props all these residuals are equivalent (each follows from
`pinchRestDone_ResidualStatement` through its first disjunct).  The new disjunct is WEAKER than
`pinchAbsSub_Rest` (`pinchAbsOut_rest_of_sub`): it drops `OUT`, which is proved when the outer
cycle follows (`pinchAbsOut_subRest_of_follows`) and expected false otherwise.  In the follows
case the remaining gap is exactly clauses (a), (c) (`pinchAbsSub_TouchTail`); in the pinched case
it is `pinchAbs_Cut` itself, with the circuit to be chosen (not every touching circuit need have
`SUB` there).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The corrected outside statement.**  A noncrossing closed walk of a disc diagram whose outer
cycle follows its boundary has an edge connected outside.  (The version with the two Euler
equalities in place of `FollowsBoundary`, `pinchAbsSub_OutsideStatement`, is FALSE.) -/
def pinchAbsOut_OutsideStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (X : DiscDiagram.{u, w, v} W) (walk : List X.toCombMap.Dart)
    (hw : IsNoncrossingClosedWalk X.toCombMap walk),
    (hw.outerCycle X.planar).FollowsBoundary → pinchAbsSub_Outside X.toCombMap walk

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsOut_OutsideStatement

/-- **The corrected outside statement holds.** -/
theorem pinchAbsOut_outsideStatement : pinchAbsOut_OutsideStatement.{u, w, v} := by
  intro G _ Lambda W X walk hw hf
  exact pinchAbsOut_outside_of_follows hw X.planar hf

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsOut_outsideStatement

section Rest

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **What is left of the absorbed lobe cut, split on `FollowsBoundary`.**  When the outer cycle
of `K.walk` follows its boundary, clauses (a) and (c); otherwise the cut itself. -/
def pinchAbsOut_Rest (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j)) (f : X.toCombMap.Face)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk) : Prop :=
  ((hw.outerCycle X.planar).FollowsBoundary → pinchAbsSub_TouchTail a b K G₁ G₂ f) ∧
    (¬ (hw.outerCycle X.planar).FollowsBoundary → pinchAbs_Cut a b K G₁ G₂ f)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsOut_Rest

/-- **In the follows case clauses (a), (c) give the rest of gl-p07-73**: `OUT` is proved. -/
theorem pinchAbsOut_subRest_of_follows {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)} {f : X.toCombMap.Face}
    {hw : IsNoncrossingClosedWalk X.toCombMap K.walk}
    (hfo : (hw.outerCycle X.planar).FollowsBoundary) (ht : pinchAbsSub_TouchTail a b K G₁ G₂ f) :
    pinchAbsSub_Rest a b K G₁ G₂ f :=
  ⟨pinchAbsOut_outside_of_follows hw X.planar hfo, ht⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsOut_subRest_of_follows

/-- **The absorbed lobe cut from the split rest.** -/
theorem pinchAbsOut_cut_of_rest {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)} {f : X.toCombMap.Face}
    {hw : IsNoncrossingClosedWalk X.toCombMap K.walk}
    (hf : f ∈ sideFaces X.toCombMap K.walk) (h : pinchAbsOut_Rest a b K G₁ G₂ f hw) :
    pinchAbs_Cut a b K G₁ G₂ f := by
  by_cases hfo : (hw.outerCycle X.planar).FollowsBoundary
  · exact pinchAbsSub_cut_of_rest hf (pinchAbsOut_subRest_of_follows hfo (h.1 hfo))
  · exact h.2 hfo

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsOut_cut_of_rest

/-- **The split rest is weaker than the rest of gl-p07-73.** -/
theorem pinchAbsOut_rest_of_sub {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)} {f : X.toCombMap.Face}
    (hf : f ∈ sideFaces X.toCombMap K.walk) (h : pinchAbsSub_Rest a b K G₁ G₂ f)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk) : pinchAbsOut_Rest a b K G₁ G₂ f hw :=
  ⟨fun _ => h.2, fun _ => pinchAbsSub_cut_of_rest hf h⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsOut_rest_of_sub

end Rest

/-- **Remaining gap of lane gl-p07-74.**  The premise block of `pinchAbsSub_ResidualStatement`
verbatim, with the conclusion `pinchFollow_Conclusion ∨ pinchAbsOut_Rest`. -/
def pinchAbsOut_ResidualStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j → Disjoint a.1 b.1 →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
    ∀ G₁ : CyclicArc (cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i →
    ∀ G₂ : CyclicArc (cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j →
    ∀ hw : IsNoncrossingClosedWalk X.toCombMap K.walk,
      X.outerFace ∉ sideFaces X.toCombMap K.walk →
      (reclosedMap X.toCombMap (sideFaces X.toCombMap K.walk)
          (hw.innerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      (reclosedMap X.toCombMap (sideOutside X.toCombMap K.walk)
          (hw.outerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      ∀ C ∈ X.relatorCells, C.face ∈ sideFaces X.toCombMap K.walk → C.face ∉ a.1 → C.face ∉ b.1 →
        ¬ (0 < (a.cellArcList i).length ∧ 0 < (a.cellArcList j).length ∧
            0 < (b.cellArcList i).length ∧ 0 < (b.cellArcList j).length ∧
            (∀ d ∈ G₁.darts, PocketRun.PinchFreeAt X.toCombMap d) ∧
            (∀ d ∈ G₂.darts, PocketRun.PinchFreeAt X.toCombMap d) ∧
            ∃ outerWalk : List X.toCombMap.Dart,
              EnclosedFaceSetSucc X (FourPieceWitness.witnessFaces a b K C.face) outerWalk ∧
                ∀ d ∈ outerWalk, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈
                  FourPieceWitness.witnessFaces a b K C.face) →
        (∀ outerWalk : List X.toCombMap.Dart,
          EnclosedFaceSetSucc X (FourPieceWitness.witnessFaces a b K C.face) outerWalk →
          (∀ d ∈ outerWalk, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈
            FourPieceWitness.witnessFaces a b K C.face) →
          ((0 < (a.cellArcList i).length ∧ 0 < (a.cellArcList j).length ∧
              0 < (b.cellArcList i).length ∧ 0 < (b.cellArcList j).length) ∨
            PinchCase.WalkDegenCaseNoninterleave b G₁ G₂ outerWalk) →
          ¬ FourPieceWitness.AbsorbFaceSetStepGood G₁ G₂ outerWalk ∧
            ∃ (p : ℕ) (hp : p < outerWalk.length),
              (outerWalk[p] ∈ G₁.darts ∨ outerWalk[p] ∈ G₂.darts) ∧
              ¬ PocketRun.PinchFreeAt X.toCombMap outerWalk[p]) →
          pinchFollow_Conclusion a b K G₁ G₂ C.face ∨ pinchAbsOut_Rest a b K G₁ G₂ C.face hw

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsOut_ResidualStatement

/-- **The `_of_` reduction of lane gl-p07-74.**  The split rest gives the absorbed lobe cut. -/
theorem pinchAbsOut_of_statement (h : pinchAbsOut_ResidualStatement.{u, w, v}) :
    pinchAbs_ResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hP
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb hcase hP with hc | hr
  · exact Or.inl hc
  · exact Or.inr (pinchAbsOut_cut_of_rest hCf hr)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsOut_of_statement

/-- **The residual of gl-p07-73 gives this one** (so this one is no stronger). -/
theorem pinchAbsOut_statement_of_sub (h : pinchAbsSub_ResidualStatement.{u, w, v}) :
    pinchAbsOut_ResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hP
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb hcase hP with hc | hr
  · exact Or.inl hc
  · exact Or.inr (pinchAbsOut_rest_of_sub hCf hr hw)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsOut_statement_of_sub

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
