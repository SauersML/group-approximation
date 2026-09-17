import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonClasses
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ShortSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shape: nodup facts for class darts and side darts

Lane `gl-p04-08` of the decomposition of `ClassPocketWindowShapeStatement`
(module `Piece04.RotationTurns`).

* `classDarts_nodup`: the darts of a class of kind `cell j` (its sides with the gaps between
  them) have no repeated dart.
* `sideDarts_disjoint`: two different sides of one polygon have no common dart.

## Proof route

*Class darts.*  By `OsinLemma94ClassPolygons.cell_arc` the class darts are
`arc.reverseDarts = arc.darts.reverse.map α` for a cyclic arc `arc` of the boundary cycle
`cellDarts S.diagram j` of the `j`-th relator cell.  That cycle is duplicate free
(`Embedded.cellDarts_nodup`, the `nodup` field of the face boundary), so `arc.darts` is
duplicate free (`CyclicArc.darts_nodup`), and so are its reverse (`List.nodup_reverse`) and its
image under the injective map `α` (`List.Nodup.map`).

*Side darts.*  The face walk of `P.face k`, rotated by `P.base k`, is
`(List.range (P.sideCount k)).flatMap (P.sideDarts k)` (`P.walk`).  The face walk is duplicate
free, so by `List.nodup_flatMap` the blocks are pairwise disjoint.  This is
`OsinLemma94RealizedPolygons.sideDarts_disjoint` (module `Estimating.OsinLemma94ShortSides`),
restated here over the lane's binder order.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.DartsNodup

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- **The darts of a cell class have no repeated dart.**  A class of kind `cell j` is the
reversed arc `arc.darts.reverse.map α` of a cyclic arc of the duplicate-free boundary cycle of
the `j`-th relator cell. -/
theorem classDarts_nodup (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i : ℕ)
    (j : Fin S.diagram.rCellCount) (hi : i < Q.classCount k)
    (hj : Q.classKind k i = .cell j) :
    (Q.classDarts k i).Nodup := by
  obtain ⟨arc, harc⟩ := Q.cell_arc k i j hi hj
  have hcd : Q.classDarts k i = arc.reverseDarts := harc
  rw [hcd]
  exact List.Nodup.map S.diagram.toCombMap.alpha_involutive.injective
    (List.nodup_reverse.mpr (CyclicArc.darts_nodup arc (cellDarts_nodup S.diagram j)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.DartsNodup.classDarts_nodup

/-- **Different sides of one polygon are disjoint.**  The sides are consecutive blocks of the
duplicate-free face walk of `P.face k`.  The class polygons `_Q` only fix the binder order of the
lane interface. -/
theorem sideDarts_disjoint (_Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (s s' : ℕ)
    (hs : s < P.sideCount k) (hs' : s' < P.sideCount k) (hne : s ≠ s') :
    List.Disjoint (P.sideDarts k s) (P.sideDarts k s') :=
  P.sideDarts_disjoint k hs hs' hne

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.DartsNodup.sideDarts_disjoint

/-- A class of kind `cell j` is duplicate free as a list of sides with gaps: every block
`P.sideDarts k s ++ Q.gap k s` of a side `s` of the class is duplicate free.  This is the
per-block half of `classDarts_nodup`, via `List.nodup_flatMap`. -/
theorem side_append_gap_nodup (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i : ℕ)
    (j : Fin S.diagram.rCellCount) (hi : i < Q.classCount k)
    (hj : Q.classKind k i = .cell j) (s : ℕ) (hs : s ∈ Q.classSides k i) :
    (P.sideDarts k s ++ Q.gap k s).Nodup := by
  have h : ((Q.classSides k i).flatMap fun t => P.sideDarts k t ++ Q.gap k t).Nodup :=
    classDarts_nodup Q k i j hi hj
  exact (List.nodup_flatMap.mp h).1 s hs

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.DartsNodup.side_append_gap_nodup

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.DartsNodup
