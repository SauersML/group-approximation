import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketKeptCellAbsorbed
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
Let `x ≠ y` be selected regions and `K` a pocket walk with the source arc and sides of
`PocketWalk.exists_of_exteriorAt`.  If no relator word has value one, the walk is noncrossing and
the faces on its side are unpinched, then the walk is simple, so a relator cell lies on its side
(`GloballyDistinguishedSectionFamily.exists_kept_of_simple_of_value`).  A side with no relator
cell is a contradiction.

* `IsNoncrossingClosedWalk.isSimpleClosedWalk_of_unpinched`: a noncrossing closed walk whose side
  is unpinched is a simple closed walk.  The proof is that of
  `PocketFaceSet.simple_of_closedWalk_of_unpinched`, run on the walk's own boundary cycle
  `IsNoncrossingClosedWalk.innerCycle`.  A pocket face set carries a relator cell `kept` on its
  side, so under `hno` there is no pocket face set to apply that lemma to.
* `GloballyDistinguishedSectionFamily.false_of_unpinched`: if no relator word has value one, an
  unpinched noncrossing pocket walk has a relator cell on its side, against `hno`.

Not proved here: `hpinch` and `hno`.  At least area, `hnc` holds under the edge conditions
(`PocketWalk.isNoncrossingClosedWalk_of_copyClean`, `Estimating/OsinPocketWalkCopyNoncrossing.lean`)
and `hvalue` holds (`leastArea_listVal_word_ne_one`, `Estimating/OsinAppendixO52Prep.lean`).  The
pinched case is not treated.

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

/-- **The unpinched pocket holds a cell.**  Let `x ≠ y` be selected regions, and `K` a pocket walk
to section `j` whose source arc spans those of `x`, a gap and `y`, whose first side is the left
side of `y` and whose second side is the right side of `x`.  If no relator word has value one, the
walk is noncrossing and the faces on its side are unpinched, then a relator cell lies on its side
(`exists_kept_of_simple_of_value`), so a side with no relator cell is a contradiction. -/
theorem false_of_unpinched
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {j : Fin cuts.count} {x y : RegionCandidate D eps S.diagram}
    (hxS : x ∈ S.family) (hyS : y ∈ S.family) (hxy : x ≠ y)
    (K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ))
    (hgap : ∃ Gap : CyclicArc (cellDarts S.diagram i),
      K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts)
    (hfirst : K.firstSide = y.2.leftSide) (hsecond : K.secondSide = x.2.rightSide)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hnc : IsNoncrossingClosedWalk S.diagram.toCombMap K.walk)
    (hpinch : Surgery.MapCollapse.Unpinched S.diagram.toCombMap
      (sideFaces S.diagram.toCombMap K.walk))
    (hno : ∀ k : Fin S.diagram.rCellCount,
      (cell S.diagram k).face ∉ sideFaces S.diagram.toCombMap K.walk) :
    False := by
  obtain ⟨kept, hkept⟩ := S.exists_kept_of_simple_of_value hxS hyS hxy K hgap hfirst hsecond
    hvalue (hnc.isSimpleClosedWalk_of_unpinched S.diagram.planar hpinch)
  exact hno kept hkept

end GloballyDistinguishedSectionFamily

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.isSimpleClosedWalk_of_unpinched
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.false_of_unpinched
