import GroupApproximation.Manuscript.NonMF.Full.GL02.RotationTurns
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shapes: the inputs of the head shape (lanes gl-p04-01 … 04)

*GL02 copy.*  Re-proof of the foreign module `Piece04.WindowShape.HeadShapeDeps`
(origin/main blob `8120da6c0`), moved to namespace `Piece04.GL02` since the modules it
imports include files last changed by commits marked WIP.  Only namespaces, the imports of
copied modules, and the qualification of foreign names differ from the original.

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  The head shape of a class window
arc (module `Piece04.WindowShape.HeadShape`) uses four facts about the class polygons.  Lanes
gl-p04-01 … gl-p04-04 prove them, in parallel with this lane.  This module states each of them as a
`Prop`, with the exact text of that lane's target, so that `HeadShape.windowHeadShape_of_deps` can
be proved now and plugged in by the assembly lane (gl-p04-13).

* `ClassStepStatement` (gl-p04-01, `ClassStep.sigma_succ`): consecutive darts `d`, `e` of a cell
  class satisfy `σ e = α d`.  True: `cell_arc` makes the class `arc.reverseDarts`, and
  `isChain_backward_reverseDarts` makes that list a `Backward` chain, `φ (α e) = α d`.
* `ClassSidesSuccStatement` (gl-p04-02, `ClassSidesSucc.succ`): the sides of a class are sides of
  the polygon, and adjacent class sides are successive mod `sideCount` (`sides_eq`).
* `SideSuccFaceStatement` (gl-p04-03, `SideSuccFace.facePerm_last`): the face permutation takes the
  last dart of side `s` to the first dart of side `s + 1 mod sideCount` (`P.walk`).
* `WindowHeadSplitStatement` (gl-p04-04, `WindowHeadSplit.split`): at a start `x` outside every gap,
  the class window is `γc ++ t :: rest` with `t` the first dart of the run window, and either
  `γc = []` or `γc` is the whole gap after a class side `s` ending at position `x - 1`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.HeadShape

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.CaseOneWalk

/-- **Class step** (lane gl-p04-01): consecutive darts `d`, `e` of a class of kind `cell j`
satisfy `σ e = α d`. -/
def ClassStepStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (i : ℕ) (j : Fin S.diagram.rCellCount), i < Q.classCount k → Q.classKind k i = .cell j →
    ∀ (n : ℕ) (d e : S.diagram.toCombMap.Dart), (Q.classDarts k i)[n]? = some d →
      (Q.classDarts k i)[n + 1]? = some e →
      S.diagram.toCombMap.sigma e = S.diagram.toCombMap.alpha d

/-- **Adjacent class sides are successive** (lane gl-p04-02). -/
def ClassSidesSuccStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (i : ℕ), i < Q.classCount k →
    (∀ s ∈ Q.classSides k i, s < P.sideCount k) ∧
      ∀ (n s s' : ℕ), (Q.classSides k i)[n]? = some s → (Q.classSides k i)[n + 1]? = some s' →
        s' = (s + 1) % P.sideCount k

/-- **Successive sides are contiguous on the face walk** (lane gl-p04-03). -/
def SideSuccFaceStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (s : ℕ), s < P.sideCount k → ∀ (d t : S.diagram.toCombMap.Dart),
      (P.sideDarts k s).getLast? = some d →
      (P.sideDarts k ((s + 1) % P.sideCount k)).head? = some t →
      S.diagram.toCombMap.facePerm d = t

/-- **Head split of a run window at a non-gap start** (lane gl-p04-04). -/
def WindowHeadSplitStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (i x y : ℕ), i < Q.classCount k → x ≤ y → y ≤ (Q.word k i).length → ¬ Q.InGap k i x →
    Q.runWindow k i x y ≠ [] →
    ∃ (t : S.diagram.toCombMap.Dart) (T' γc rest : List S.diagram.toCombMap.Dart),
      Q.runWindow k i x y = t :: T' ∧ Q.classWindow k i x y = γc ++ t :: rest ∧
      (γc = [] ∨ ∃ (n s s' : ℕ) (d w : S.diagram.toCombMap.Dart), 0 < x ∧
        (Q.classDarts k i)[x - 1]? = some d ∧ (Q.classDarts k i)[x]? = some w ∧
        γc.head? = some w ∧ γc = Q.gap k s ∧ (Q.classSides k i)[n]? = some s ∧
        (Q.classSides k i)[n + 1]? = some s' ∧ (P.sideDarts k s).getLast? = some d ∧
        (P.sideDarts k s').head? = some t)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.HeadShape
