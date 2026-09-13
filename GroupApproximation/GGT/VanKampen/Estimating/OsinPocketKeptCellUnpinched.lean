import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketKeptCell
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionUnpinched
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# The unpinched pocket between two exterior regions holds a cell

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(a): "otherwise one can include the
ε-contiguity subdiagrams corresponding to the edges `e` and `f` of `Φ'_M` into a single
ε-contiguity subdiagram in the obvious way, contrary to the definition of `M`."

The simple case of the two-gon premise `TwoGonHoldsInput`, stated on the diagram of any globally
distinguished family, in particular the thickened family `S'` of `OuterSpurThickeningStatement`.
Let `x ≠ y` be exterior regions of one cell to one section, and `K` their pocket walk, as given by
`PocketWalk.exists_of_exteriorAt`.  If the walk is noncrossing and the faces on its side are
unpinched, the walk is simple, so a relator cell lies on its side
(`GloballyDistinguishedSectionFamily.exists_kept_of_simple`).  A side with no relator cell is a
contradiction.

* `IsNoncrossingClosedWalk.isSimpleClosedWalk_of_unpinched`: a noncrossing closed walk whose side
  is unpinched is a simple closed walk.  The proof is that of
  `PocketFaceSet.simple_of_closedWalk_of_unpinched`, run on the walk's own boundary cycle
  `IsNoncrossingClosedWalk.innerCycle`.  A pocket face set carries a relator cell `kept` on its
  side, so under `hno` there is no pocket face set to apply that lemma to.
* `GloballyDistinguishedSectionFamily.false_of_unpinched`: if every other selected region avoids
  the side, an unpinched noncrossing pocket walk has a relator cell on its side, against `hno`.

Not proved here: `hnc`, `hpinch`, `hno` and `havoid`.  The pinched case is not treated.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7;
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

namespace IsNoncrossingClosedWalk

variable {M : CombMap.{v}} {w : List M.Dart}

/-- **An unpinched noncrossing walk is simple.**  The walk is the boundary cycle `innerCycle` of
the faces on its side, so an unpinched side makes the darts of the walk start at distinct
vertices.  The other fields of a simple closed walk are fields of a noncrossing one. -/
theorem isSimpleClosedWalk_of_unpinched (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hpinch : Surgery.MapCollapse.Unpinched M (sideFaces M w)) : IsSimpleClosedWalk M w :=
  ⟨hw.ne_nil, hw.chain, hw.closes, ((hw.innerCycle hM).unpinched_iff_nodup).mp hpinch,
    hw.alpha_not_mem⟩

end IsNoncrossingClosedWalk

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}

namespace GloballyDistinguishedSectionFamily

/-- **The unpinched pocket holds a cell.**  Let `x ≠ y` be exterior regions of the cell `i` to
section `j`, and `K` their pocket walk, as given by `PocketWalk.exists_of_exteriorAt`.  If the walk
is noncrossing, the faces on its side are unpinched, and every other selected region avoids them,
then a relator cell lies on its side (`exists_kept_of_simple`), so a side with no relator cell is a
contradiction. -/
theorem false_of_unpinched
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {j : Fin cuts.count} {x y : RegionCandidate D eps S.diagram}
    (hx : x ∈ RegionCandidate.exteriorAt S.family i)
    (hy : y ∈ RegionCandidate.exteriorAt S.family i) (hxy : x ≠ y)
    (hjx : RegionCandidate.TargetsSectionIndex cuts j x)
    (hjy : RegionCandidate.TargetsSectionIndex cuts j y)
    (K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ))
    (hgap : ∃ Gap : CyclicArc (cellDarts S.diagram i),
      K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts)
    (hstart : K.targetArc.start.1 = x.2.targetArc.start.1)
    (hend : K.targetArc.start.1 + K.targetArc.length =
      y.2.targetArc.start.1 + y.2.targetArc.length)
    (hnc : IsNoncrossingClosedWalk S.diagram.toCombMap K.walk)
    (hpinch : Surgery.MapCollapse.Unpinched S.diagram.toCombMap
      (sideFaces S.diagram.toCombMap K.walk))
    (hno : ∀ k : Fin S.diagram.rCellCount,
      (cell S.diagram k).face ∉ sideFaces S.diagram.toCombMap K.walk)
    (havoid : ∀ z ∈ S.family, z ≠ x → z ≠ y →
      Disjoint z.1 (sideFaces S.diagram.toCombMap K.walk)) :
    False := by
  obtain ⟨kept, hkept⟩ := S.exists_kept_of_simple hx hy hxy hjx hjy K hgap hstart hend
    (hnc.isSimpleClosedWalk_of_unpinched S.diagram.planar hpinch) havoid
  exact hno kept hkept

end GloballyDistinguishedSectionFamily

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.isSimpleClosedWalk_of_unpinched
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.false_of_unpinched
