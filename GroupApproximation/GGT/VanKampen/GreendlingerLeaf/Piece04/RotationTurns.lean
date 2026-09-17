import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurnsClose
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.PocketTurns
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04: the class pocket rotation and turns from the window shapes

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  This module reduces
`ClassPocketRotationTurnStatement` (module `Piece04.PocketTurns`) to
`ClassPocketWindowShapeStatement`.  The new statement keeps the rotation `q B p A` of `∂Π`.  It
replaces the two first-turn closedness conclusions by the shape of the four window ends
(`RotationTurns.WindowHeadShape`, `RotationTurns.WindowTailShape`).

## The isolated statement `ClassPocketWindowShapeStatement` (OPEN)

*Why it is true.*  Write `Γ = P.face k`, `Π = cell j`, and let `c_0 c_1 …` be the class darts
(`classDarts`, sides with gaps).

1. *Rotation.*  This is step 1 of the argument in `Piece04.RCellEnclosure`.  Each window contains a
   side dart (`runWindow_source_ne_nil`, `runWindow_target_ne_nil`), and gaps are loops at pinch
   vertices of `∂Π` carrying no dart of `Γ`.  So the two windows are disjoint cyclic arcs of `∂Π`.
2. *Consecutive class darts.*  By `cell_arc` the class is `arc.reverseDarts` for one arc of `∂Π`.
   So consecutive class darts `c_i`, `c_(i+1)` satisfy `φ (α c_(i+1)) = α c_i`, that is
   `σ c_(i+1) = α c_i`.  Consecutive class sides `s`, `s+1` are consecutive on `∂Γ`
   (`sides_eq`), so `φ (side_s.last) = side_(s+1).head`.  Sides are nonempty.
3. *Head of a window.*  `T = runWindow` is the side darts of the window in order, and
   `q = targetArc.darts` is the window reversed and mapped by `α`.  Let `t = T.head`.  Then
   `q = q' (α t) γ`, where `γ` reverses the gap darts of the window in front of `t`.  No endpoint
   lies strictly inside a gap (`hnogap`).  So either `γ = []`, or the window starts at the end of
   a side `s` and contains the whole gap `gap_s`.  In the second case `t = side_(s+1).head`,
   `γ.last = α (gap_s.head)`, and by step 2
   `σ (φ γ.last) = σ (σ gap_s.head) = σ (α side_s.last) = φ side_s.last = t`.
4. *Tail of a window.*  Let `u = U.last`, and write `p = γ (α u) p'`.  Either `γ = []`, or the
   window ends at the start of side `s+1` and contains the whole gap `gap_s` (`gap_last`: a class
   ends with a side), with `u = side_s.last`.  Then
   `γ.head = α (gap_s.last) = σ side_(s+1).head = σ (φ u)`.

Both windows have both shapes, since the head and tail arguments do not depend on the orientation.

## The reduction proved here

`rotationTurns_of_windowShape` builds a `RotationTurns.PocketSetting`:

* walk `X T Y U` with `T`, `U` the run windows;
* carrier `q B p A`;
* `face_ne` from `face_not_cell`;
* crossing darts from `mem_classWindow_of_mem_runWindow`.

`RotationTurns.firstTurnClosed_X` and `firstTurnClosed_Y` then close `B X` and `A Y`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.CaseOneWalk

/-- **The class pocket window shapes** (OPEN).  For a backwards class pair of one relator cell `Π`,
with no endpoint inside a gap, `∂Π` rotates to `q B p A`.  Moreover, both run windows have the head
shape and the tail shape against their class window arcs. -/
def ClassPocketWindowShapeStatement : Prop :=
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
        RotationTurns.WindowHeadShape S.diagram.toCombMap (Q.runWindow k C.target C.b' C.b)
          targetArc.darts ∧
        RotationTurns.WindowTailShape S.diagram.toCombMap (Q.runWindow k C.target C.b' C.b)
          targetArc.darts ∧
        RotationTurns.WindowHeadShape S.diagram.toCombMap (Q.runWindow k C.source C.a C.a')
          sourceArc.darts ∧
        RotationTurns.WindowTailShape S.diagram.toCombMap (Q.runWindow k C.source C.a C.a')
          sourceArc.darts

/-- **The class pocket rotation and turns from the window shapes.** -/
theorem rotationTurns_of_windowShape (h : ClassPocketWindowShapeStatement.{u, w, v}) :
    ClassPocketRotationTurnStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts S P Q k C hback hnogap j sourceArc targetArc X Y r
    hks hkt htrav hsource htarget
  obtain ⟨n, B, A, hPi, headT, tailT, headU, tailU⟩ :=
    h Q k C hback hnogap j sourceArc targetArc X Y r hks hkt htrav hsource htarget
  have hcell : S.diagram.toCombMap.IsFaceCycle (cellDarts S.diagram j) :=
    (S.diagram.faceBoundary (cell S.diagram j).face).isFaceCycle
  have hset : RotationTurns.PocketSetting S.diagram.toCombMap X
      (Q.runWindow k C.target C.b' C.b) Y (Q.runWindow k C.source C.a C.a')
      targetArc.darts B sourceArc.darts A :=
    { planar := S.diagram.planar
      walk := RotationTurns.faceCycle_of_eq
        ((S.diagram.faceBoundary (P.face k)).isFaceCycle.rotate r) htrav
      carrier := RotationTurns.faceCycle_of_eq (hcell.rotate n) hPi
      face_ne := fun x hx y hy hxy => P.face_not_cell k j
        ((SameCellPocketSides.faceOf_of_mem_cellDarts_rotate hPi hy).symm.trans
          (hxy.symm.trans (SameCellPocketSides.faceOf_of_mem_rotate htrav hx)))
      cross_T := fun d hd => by
        have hd' : d ∈ targetArc.darts.reverse.map S.diagram.toCombMap.alpha := by
          show d ∈ targetArc.reverseDarts
          rw [htarget]
          exact mem_classWindow_of_mem_runWindow Q k hback.le hd
        exact FirstTurnWalk.mem_reverse_map_alpha_iff.mp hd'
      cross_U := fun d hd => by
        have hd' : d ∈ sourceArc.darts.reverse.map S.diagram.toCombMap.alpha := by
          show d ∈ sourceArc.reverseDarts
          rw [hsource]
          exact mem_classWindow_of_mem_runWindow Q k C.source_forward.le hd
        exact FirstTurnWalk.mem_reverse_map_alpha_iff.mp hd'
      headT := headT
      tailU := tailU }
  exact ⟨n, B, A, hPi, RotationTurns.firstTurnClosed_X hset,
    RotationTurns.firstTurnClosed_Y hset headU tailT⟩

/-- **The relator-cell branch of GapSpan from the class pocket window shapes.** -/
theorem rCell_of_windowShape (h : ClassPocketWindowShapeStatement.{u, w, v}) :
    OsinLemma94ClassCaseOneRCellStatement.{u, w, v} :=
  rCell_of_classPocketRotationTurns (rotationTurns_of_windowShape h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.rotationTurns_of_windowShape
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.rCell_of_windowShape
