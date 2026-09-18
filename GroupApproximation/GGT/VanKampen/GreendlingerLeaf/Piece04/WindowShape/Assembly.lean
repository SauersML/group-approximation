import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shapes: assembly of `ClassPocketWindowShapeStatement`

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  This module assembles
`Piece04.ClassPocketWindowShapeStatement` (module `Piece04.RotationTurns`) from three pieces:

* `HeadShapeStatement` (lane gl-p04-06, `WindowShape.HeadShape.windowHeadShape`): a run window that
  starts off a gap has the head shape against the arc of its class window.
* `TailShapeStatement` (lane gl-p04-07, `WindowShape.TailShape.windowTailShape`): a run window that
  ends off a gap has the tail shape against the arc of its class window.
* `CellRotationStatement` (lane gl-p04-12, `WindowShape.CellRotation.exists_rotate`): `∂Π` rotates
  to `q B p A`.

Those lanes run in parallel and their modules are not on disk yet, so their targets are stated here
with the exact lane text, and the endpoints are the reductions `windowShape_of_shapes` and
`proof_of_shapes`.  `CellRotationStatement` keeps every hypothesis of
`ClassPocketWindowShapeStatement`, so it is the weakest form of lane 12, and any version of lane 12
that drops unused hypotheses implies it.  Once the three lanes land, the unconditional endpoint is

```
theorem windowShape : ClassPocketWindowShapeStatement.{u, w, v} :=
  windowShape_of_shapes HeadShape.windowHeadShape TailShape.windowTailShape
    CellRotation.exists_rotate
```

## Why it is true (the assembly)

* Rotation: lane 12, with the hypotheses unchanged.
* Target window, `i = C.target`, `(x, y) = (C.b', C.b)`: `x ≤ y` is `hback.le`, `y ≤ |word|` is
  `C.b_le`, and the class index bound is `C.target_lt`.  Neither endpoint lies in a gap, by
  `hnogap` (the last two disjuncts of `GapEndpoint`).  The window is nonempty by
  `runWindow_target_ne_nil`.  Lane 06 gives the head shape and lane 07 the tail shape.
* Source window, `i = C.source`, `(x, y) = (C.a, C.a')`: `C.source_forward.le`, `C.a'_le`,
  `C.source_lt`, the first two disjuncts of `hnogap`, and `runWindow_source_ne_nil`.
* `C` is a connector pair over `Q.word k`, so `C.b_le : C.b ≤ (Q.word k C.target).length`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.Assembly

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.CaseOneWalk

/-- **Head shape of a class window arc** (lane gl-p04-06, not yet on disk).  A run window of a
cell-`j` class that starts off a gap and is nonempty has the head shape against the arc of its class
window. -/
def HeadShapeStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (i : ℕ) (j : Fin S.diagram.rCellCount) (x y : ℕ) (arc : CyclicArc (cellDarts S.diagram j)),
    i < Q.classCount k → Q.classKind k i = .cell j → x ≤ y → y ≤ (Q.word k i).length →
    ¬ Q.InGap k i x → Q.runWindow k i x y ≠ [] → arc.reverseDarts = Q.classWindow k i x y →
    RotationTurns.WindowHeadShape S.diagram.toCombMap (Q.runWindow k i x y) arc.darts

/-- **Tail shape of a class window arc** (lane gl-p04-07, not yet on disk).  A run window of a
cell-`j` class that ends off a gap and is nonempty has the tail shape against the arc of its class
window. -/
def TailShapeStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (i : ℕ) (j : Fin S.diagram.rCellCount) (x y : ℕ) (arc : CyclicArc (cellDarts S.diagram j)),
    i < Q.classCount k → Q.classKind k i = .cell j → x ≤ y → y ≤ (Q.word k i).length →
    ¬ Q.InGap k i y → Q.runWindow k i x y ≠ [] → arc.reverseDarts = Q.classWindow k i x y →
    RotationTurns.WindowTailShape S.diagram.toCombMap (Q.runWindow k i x y) arc.darts

/-- **Rotation of the cell to `q B p A`** (lane gl-p04-12, not yet on disk).  Under the hypotheses
of `ClassPocketWindowShapeStatement`, `∂Π` rotates to the target arc, a complement, the source arc
and a complement. -/
def CellRotationStatement : Prop :=
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
        (cellDarts S.diagram j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A

/-- **The class pocket window shapes from the head shape, the tail shape and the rotation.** -/
theorem windowShape_of_shapes (hhead : HeadShapeStatement.{u, w, v})
    (htail : TailShapeStatement.{u, w, v}) (hrot : CellRotationStatement.{u, w, v}) :
    ClassPocketWindowShapeStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts S P Q k C hback hnogap j sourceArc targetArc X Y r
    hks hkt htrav hsource htarget
  obtain ⟨n, B, A, hPi⟩ :=
    hrot Q k C hback hnogap j sourceArc targetArc X Y r hks hkt htrav hsource htarget
  have hngA : ¬ Q.InGap k C.source C.a := fun h => hnogap (Or.inl h)
  have hngA' : ¬ Q.InGap k C.source C.a' := fun h => hnogap (Or.inr (Or.inl h))
  have hngB : ¬ Q.InGap k C.target C.b := fun h => hnogap (Or.inr (Or.inr (Or.inl h)))
  have hngB' : ¬ Q.InGap k C.target C.b' := fun h => hnogap (Or.inr (Or.inr (Or.inr h)))
  have hT : Q.runWindow k C.target C.b' C.b ≠ [] := runWindow_target_ne_nil Q k C hback hnogap
  have hU : Q.runWindow k C.source C.a C.a' ≠ [] := runWindow_source_ne_nil Q k C hnogap
  exact ⟨n, B, A, hPi,
    hhead Q k C.target j C.b' C.b targetArc C.target_lt hkt hback.le C.b_le hngB' hT htarget,
    htail Q k C.target j C.b' C.b targetArc C.target_lt hkt hback.le C.b_le hngB hT htarget,
    hhead Q k C.source j C.a C.a' sourceArc C.source_lt hks C.source_forward.le C.a'_le hngA hU
      hsource,
    htail Q k C.source j C.a C.a' sourceArc C.source_lt hks C.source_forward.le C.a'_le hngA' hU
      hsource⟩

/-- **The class pocket window shapes** (lane gl-p04-13 endpoint, `proof` spelling), from the three
upstream lane targets. -/
theorem proof_of_shapes (hhead : HeadShapeStatement.{u, w, v})
    (htail : TailShapeStatement.{u, w, v}) (hrot : CellRotationStatement.{u, w, v}) :
    ClassPocketWindowShapeStatement.{u, w, v} :=
  windowShape_of_shapes hhead htail hrot

/-- **The relator-cell branch of GapSpan from the three upstream lane targets.** -/
theorem rCell_of_shapes (hhead : HeadShapeStatement.{u, w, v})
    (htail : TailShapeStatement.{u, w, v}) (hrot : CellRotationStatement.{u, w, v}) :
    OsinLemma94ClassCaseOneRCellStatement.{u, w, v} :=
  rCell_of_windowShape (windowShape_of_shapes hhead htail hrot)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.Assembly

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.Assembly.windowShape_of_shapes
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.Assembly.proof_of_shapes
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.Assembly.rCell_of_shapes
