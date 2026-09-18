import GroupApproximation.Manuscript.NonMF.Full.GL02.PocketTurns
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94OneCellSameCell
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shape: the rotation of the cell to `q B p A`

*GL02 copy.*  Re-proof of the foreign module `Piece04.WindowShape.CellRotation`
(origin/main blob `a731adc9f`), moved to namespace `Piece04.GL02` since the modules it
imports include files last changed by commits marked WIP.  Only namespaces, the imports of
copied modules, and the qualification of foreign names differ from the original.

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  This module proves the rotation
conjunct of `ClassPocketWindowShapeStatement` (module `Piece04.RotationTurns`) from the
disjointness of the class darts of two distinct classes of one relator cell (lane `gl-p04-11`,
stated here as `ClassDisjointStatement` because that module is not on disk yet).

## The argument

Let `Π = cell j`, `q = targetArc.darts`, `p = sourceArc.darts`.

1. *Nonempty arcs.*  The run windows are nonempty (`runWindow_target_ne_nil`,
   `runWindow_source_ne_nil`), each run window dart lies in the class window
   (`mem_classWindow_of_mem_runWindow`), and the class window is `arc.reverseDarts`.  So the arc
   has a dart, hence positive length (`CyclicArc.darts_length`).
2. *Disjoint arcs.*  If `d ∈ p` and `d ∈ q`, then `α d` lies in both `sourceArc.reverseDarts`
   and `targetArc.reverseDarts`, that is, in both class windows.  A class window
   `((classDarts k i).drop x).take (y - x)` is contained in `classDarts k i`.  So `α d` is a class
   dart of both `C.source` and `C.target`.  These are distinct classes (`C.distinct`) below
   `classCount k` (`C.source_lt`, `C.target_lt`) of the same kind `.cell j`, whose class darts are
   disjoint (`ClassDisjointStatement`).  Contradiction.
3. `CaseOneSameCell.exists_rotate_eq_append_four` gives `∂Π.rotate n = q B p A`.

## Endpoints

* `rotate_of_classDisjoint`: the rotation, from `ClassDisjointStatement`, taking only the
  hypotheses it uses (the face-walk rotation `htrav` and its `X`, `Y`, `r` are not needed).
* `exists_rotate_of_classDisjoint : ClassDisjointStatement → CellRotationStatement`, where
  `CellRotationStatement` has every binder and hypothesis of `ClassPocketWindowShapeStatement`,
  with the same text as the `CellRotationStatement` of module `WindowShape.Assembly`.  Once lane
  `gl-p04-11` lands, `exists_rotate := exists_rotate_of_classDisjoint ClassDisjoint.disjoint`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.CellRotation

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.CaseOneWalk

/-- **Class darts of distinct classes are disjoint** (lane `gl-p04-11`, not yet on disk).  Two
distinct classes of polygon `k` of the same relator-cell kind have no common class dart. -/
def ClassDisjointStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    {P : OsinLemma94RealizedPolygons S} (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (i i' : ℕ) (j : Fin S.diagram.rCellCount),
    i < Q.classCount k → i' < Q.classCount k → i ≠ i' →
    Q.classKind k i = .cell j → Q.classKind k i' = .cell j →
    List.Disjoint (Q.classDarts k i) (Q.classDarts k i')

/-- The reversal `α d` of a dart of an arc is a dart of the reversed arc. -/
theorem alpha_mem_reverseDarts {M : CombMap.{v}} {cycle : List M.Dart} (arc : CyclicArc cycle)
    {d : M.Dart} (hd : d ∈ arc.darts) : M.alpha d ∈ arc.reverseDarts := by
  show M.alpha d ∈ arc.darts.reverse.map M.alpha
  exact List.mem_map.mpr ⟨d, List.mem_reverse.mpr hd, rfl⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.CellRotation.alpha_mem_reverseDarts

/-- An arc whose reversal contains a nonempty list has positive length. -/
theorem length_pos_of_sub_reverseDarts {M : CombMap.{v}} {cycle : List M.Dart}
    (arc : CyclicArc cycle) {T : List M.Dart} (hT : T ≠ [])
    (hsub : ∀ s ∈ T, s ∈ arc.reverseDarts) : 0 < arc.length := by
  obtain ⟨d, hd, -⟩ := exists_cross_of_ne_nil arc hT hsub
  rw [← arc.darts_length]
  exact List.length_pos_of_mem hd

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.CellRotation.length_pos_of_sub_reverseDarts

section Rotation

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- A dart of a class window is a class dart. -/
theorem mem_classDarts_of_mem_classWindow (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    {i x y : ℕ} {d : S.diagram.toCombMap.Dart} (hd : d ∈ Q.classWindow k i x y) :
    d ∈ Q.classDarts k i := by
  have hd' : d ∈ ((Q.classDarts k i).drop x).take (y - x) := hd
  exact List.mem_of_mem_drop (List.mem_of_mem_take hd')

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.CellRotation.mem_classDarts_of_mem_classWindow

/-- **The rotation of the cell to `q B p A`**, from the disjointness of distinct cell classes. -/
theorem rotate_of_classDisjoint (hdisj : ClassDisjointStatement.{u, w, v})
    (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k) (Q.classCount k)
      (Q.relatorClasses k) (Q.longClasses k) eps)
    (hback : C.b' < C.b) (hnogap : ¬ Q.GapEndpoint k C)
    (j : Fin S.diagram.rCellCount) (sourceArc targetArc : CyclicArc (cellDarts S.diagram j))
    (hks : Q.classKind k C.source = .cell j) (hkt : Q.classKind k C.target = .cell j)
    (hsource : sourceArc.reverseDarts = Q.classWindow k C.source C.a C.a')
    (htarget : targetArc.reverseDarts = Q.classWindow k C.target C.b' C.b) :
    ∃ (n : ℕ) (B A : List S.diagram.toCombMap.Dart),
      (cellDarts S.diagram j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A := by
  have hq : 0 < targetArc.length :=
    length_pos_of_sub_reverseDarts targetArc (runWindow_target_ne_nil Q k C hback hnogap)
      fun _ hs => by
        rw [htarget]
        exact mem_classWindow_of_mem_runWindow Q k hback.le hs
  have hp : 0 < sourceArc.length :=
    length_pos_of_sub_reverseDarts sourceArc (runWindow_source_ne_nil Q k C hnogap)
      fun _ hs => by
        rw [hsource]
        exact mem_classWindow_of_mem_runWindow Q k C.source_forward.le hs
  refine CaseOneSameCell.exists_rotate_eq_append_four targetArc sourceArc hq hp ?_
  intro d hds hdt
  have hs : S.diagram.toCombMap.alpha d ∈ Q.classDarts k C.source := by
    have h := alpha_mem_reverseDarts sourceArc hds
    rw [hsource] at h
    exact mem_classDarts_of_mem_classWindow Q k h
  have ht : S.diagram.toCombMap.alpha d ∈ Q.classDarts k C.target := by
    have h := alpha_mem_reverseDarts targetArc hdt
    rw [htarget] at h
    exact mem_classDarts_of_mem_classWindow Q k h
  exact hdisj Q k C.source C.target j C.source_lt C.target_lt C.distinct hks hkt hs ht

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.CellRotation.rotate_of_classDisjoint

end Rotation

/-- **The rotation of the cell to `q B p A`** (the target of lane `gl-p04-12`).  Under the
hypotheses of `ClassPocketWindowShapeStatement`, `∂Π` rotates to the target arc, a complement,
the source arc and a complement. -/
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

/-- **The cell rotation from the class disjointness.** -/
theorem exists_rotate_of_classDisjoint (hdisj : ClassDisjointStatement.{u, w, v}) :
    CellRotationStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts S P Q k C hback hnogap j sourceArc targetArc
    _ _ _ hks hkt _ hsource htarget
  exact rotate_of_classDisjoint hdisj Q k C hback hnogap j sourceArc targetArc hks hkt
    hsource htarget

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.CellRotation.exists_rotate_of_classDisjoint

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.CellRotation
