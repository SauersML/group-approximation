import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellKeptCell
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionInnerFollows
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionNoncrossingWalk
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkEuler
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeLakeModel
import GroupApproximation.Meta.AxiomGuard

/-!
# The kept cell of a noncrossing pocket walk between two cells

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): two distinct selected regions joining the
same two distinct cells `Π_i` and `Π_j` bound a subdiagram `Γ_1` with `∂Γ_1 = s_1 t_1 s_2 t_2`
containing both regions.  If `Γ_1` held no relator cell, the regions could be merged into one
contiguity region from `Π_i` to `Π_j`, "contrary to the definition" of the distinguished system.

`GloballyDistinguishedSectionFamily.exists_kept_of_cellPocketRegion_of_value`
(`Estimating/OsinPocketCellKeptCell.lean`, step 5 of the binder-5 route) gives a relator cell in any
pocket region whose cycle is the cell pocket walk.  The hypothesis `hkept` of
`CellPocketWalk.exists_cellPocketFaceSet_closedWalk_of_orient` (`Estimating/OsinPocketCellFaceSet`)
asks for a relator cell on the side of the walk itself, before the pinch makes it simple.  A
noncrossing walk bounds a pocket region on its side once the exterior face is off that side and
one of its two boundary cycles follows its boundary.
- When the outer cycle follows, `PocketRegion.ofNoncrossingClosedWalk` builds it, with the Euler
  equality from `IsNoncrossingClosedWalk.reclosed_euler`.
- When the inner cycle follows, `PocketRegion.ofNoncrossingClosedWalkInner`
  (`Estimating/OsinPocketRegionInnerFollows`) builds it.  This is the lake, where the outer cycle
  does not follow (`OsinPocketMultipleEdgeLakeModel`).
Either way its faces are the side of the walk and its cycle is the walk, so step 5 applies.

* `PocketRegion.exists_of_noncrossing_of_eitherFollows`: the pocket region of a noncrossing walk
  with either boundary cycle following.
* `GloballyDistinguishedSectionFamily.exists_kept_of_noncrossingCellWalk_of_value` and
  `_of_leastArea`: a relator cell on the side of a noncrossing cell pocket walk.
* `CellPocketKeptCellNoncrossingStatement`, `cellPocketKeptCellNoncrossing`: the same at least area,
  as a closed proposition.
* `OsinPocketCellKeptCellNoncrossing.multipleEdgeLakeInnerBranch` (model test): on the lake map of
  `OsinPocketMultipleEdgeLakeModel` the face across the dart `3` is off the side of the walk
  `[0,2,5]`, its inner cycle follows its boundary and its outer cycle does not.  So the inner
  builder's hypotheses hold there and the outer builder's do not.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

namespace PocketRegion

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} {walk : List Delta.toCombMap.Dart}

/-- **The pocket region of a noncrossing walk with either boundary cycle following.**  If the
exterior face is off the side of a noncrossing closed walk and its outer cycle or its inner cycle
follows its boundary, there is a pocket region whose faces are the side of the walk and whose cycle
is the walk. -/
theorem exists_of_noncrossing_of_eitherFollows (hw : IsNoncrossingClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk)
    (hfollow : (hw.outerCycle Delta.planar).FollowsBoundary ∨
      (hw.innerCycle Delta.planar).FollowsBoundary) :
    ∃ P : PocketRegion Delta, P.faces = sideFaces Delta.toCombMap walk ∧ P.inner.cycle = walk := by
  rcases hfollow with hfollows | hin
  · exact ⟨ofNoncrossingClosedWalk hw hout hfollows (hw.reclosed_euler Delta.planar hfollows),
      rfl, rfl⟩
  · exact ⟨ofNoncrossingClosedWalkInner hw hout hin, rfl, rfl⟩

end PocketRegion

namespace GloballyDistinguishedSectionFamily

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The kept cell of a noncrossing pocket walk between two cells, from the values of the relator
words.**  Let `a ≠ b` be selected regions joining the distinct cells `i` and `j`, and `K` a cell
pocket walk whose first side is the side of `b` leaving `Π_j`, whose second side is the side of `a`
leaving `Π_i`, and whose arc of `Π_i` spans the arc of `a`, a gap and the arc of `b`.  If no relator
word has value one, the walk is noncrossing, the exterior face is off its side and its outer or its
inner cycle follows its boundary, then a relator cell lies on the side of the walk. -/
theorem exists_kept_of_noncrossingCellWalk_of_value
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ S.family) (hb : b ∈ S.family) (hab : a ≠ b) (hij : i ≠ j)
    (hai : a.JoinsCells i j) (hbi : b.JoinsCells i j) (K : CellPocketWalk D eps S.diagram i j)
    (hfirst : K.firstSide = b.sideFrom j) (hsecond : K.secondSide = a.sideFrom i)
    (h₁ : ∃ G₁ : CyclicArc (cellDarts S.diagram i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hw : IsNoncrossingClosedWalk S.diagram.toCombMap K.walk)
    (hout : S.diagram.outerFace ∉ sideFaces S.diagram.toCombMap K.walk)
    (hfollow : (hw.outerCycle S.diagram.planar).FollowsBoundary ∨
      (hw.innerCycle S.diagram.planar).FollowsBoundary) :
    ∃ kept : Fin S.diagram.rCellCount,
      (cell S.diagram kept).face ∈ sideFaces S.diagram.toCombMap K.walk := by
  obtain ⟨P, hfaces, hinner⟩ :=
    PocketRegion.exists_of_noncrossing_of_eitherFollows hw hout hfollow
  obtain ⟨kept, hkept⟩ := S.exists_kept_of_cellPocketRegion_of_value ha hb hab hij hai hbi K
    hfirst hsecond h₁ hvalue P hinner
  refine ⟨kept, ?_⟩
  rw [← hfaces]
  exact hkept

/-- **The kept cell of a noncrossing pocket walk between two cells at least area.**  With `a`, `b`
and `K` as in `exists_kept_of_noncrossingCellWalk_of_value`, if the diagram has least area, the
walk is noncrossing, the exterior face is off its side and one of its boundary cycles follows its
boundary, then a relator cell lies on the side of the walk. -/
theorem exists_kept_of_noncrossingCellWalk_of_leastArea
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ S.family) (hb : b ∈ S.family) (hab : a ≠ b) (hij : i ≠ j)
    (hai : a.JoinsCells i j) (hbi : b.JoinsCells i j) (K : CellPocketWalk D eps S.diagram i j)
    (hfirst : K.firstSide = b.sideFrom j) (hsecond : K.secondSide = a.sideFrom i)
    (h₁ : ∃ G₁ : CyclicArc (cellDarts S.diagram i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (hlea : S.diagram.LeastArea)
    (hw : IsNoncrossingClosedWalk S.diagram.toCombMap K.walk)
    (hout : S.diagram.outerFace ∉ sideFaces S.diagram.toCombMap K.walk)
    (hfollow : (hw.outerCycle S.diagram.planar).FollowsBoundary ∨
      (hw.innerCycle S.diagram.planar).FollowsBoundary) :
    ∃ kept : Fin S.diagram.rCellCount,
      (cell S.diagram kept).face ∈ sideFaces S.diagram.toCombMap K.walk :=
  S.exists_kept_of_noncrossingCellWalk_of_value ha hb hab hij hai hbi K hfirst hsecond h₁
    (fun C hC => DiscDiagram.leastArea_listVal_word_ne_one hlea C hC) hw hout hfollow

end GloballyDistinguishedSectionFamily

/-- **A relator cell on the side of a noncrossing pocket walk between two cells** (binder 5,
residual (3) of the cell route).  For a globally distinguished family of a least-area diagram,
distinct selected regions `a`, `b` joining the distinct cells `i`, `j`, and a cell pocket walk `K`
with the sides of `b` and `a` and an arc of `Π_i` spanning the arcs of `a` and `b`: if the walk is
noncrossing, the exterior face is off its side and its outer or its inner cycle follows its
boundary, then a relator cell lies on its side. -/
def CellPocketKeptCellNoncrossingStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram},
    a ∈ S.family → b ∈ S.family → a ≠ b → i ≠ j → a.JoinsCells i j → b.JoinsCells i j →
      ∀ K : CellPocketWalk D eps S.diagram i j,
        K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
        (∃ G₁ : CyclicArc (cellDarts S.diagram i),
          K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) →
        S.diagram.LeastArea →
        ∀ hw : IsNoncrossingClosedWalk S.diagram.toCombMap K.walk,
          S.diagram.outerFace ∉ sideFaces S.diagram.toCombMap K.walk →
          ((hw.outerCycle S.diagram.planar).FollowsBoundary ∨
            (hw.innerCycle S.diagram.planar).FollowsBoundary) →
          ∃ kept : Fin S.diagram.rCellCount,
            (cell S.diagram kept).face ∈ sideFaces S.diagram.toCombMap K.walk

theorem cellPocketKeptCellNoncrossing : CellPocketKeptCellNoncrossingStatement.{u, w, v} := by
  intro G _ Lambda W D eps lambda c Delta cuts S i j a b ha hb hab hij hai hbi K hfirst hsecond h₁
    hlea hw hout hfollow
  exact S.exists_kept_of_noncrossingCellWalk_of_leastArea ha hb hab hij hai hbi K hfirst hsecond
    h₁ hlea hw hout hfollow

namespace OsinPocketCellKeptCellNoncrossing

/-- **The lake map under the two builders** (model test).  On the lake map of
`OsinPocketMultipleEdgeLakeModel`, the face across the dart `3`, the outside `O = [3,6]`, is off the
side of the noncrossing walk `[0,2,5]`, the inner cycle of the walk follows its boundary and its
outer cycle does not.  So `PocketRegion.ofNoncrossingClosedWalkInner` has its hypotheses there and
`PocketRegion.ofNoncrossingClosedWalk` does not. -/
def MultipleEdgeLakeInnerBranch : Prop :=
  OsinPocketMultipleEdgeLakeModel.M.faceOf (3 : OsinPocketMultipleEdgeLakeModel.M.Dart) ∉
      sideFaces OsinPocketMultipleEdgeLakeModel.M ([0, 2, 5] : List (Fin 8)) ∧
    (OsinPocketMultipleEdgeLakeModel.isNoncrossingClosedWalk_pocketCycle.innerCycle
      OsinPocketMultipleEdgeLakeModel.planar).FollowsBoundary ∧
    ¬ (OsinPocketMultipleEdgeLakeModel.isNoncrossingClosedWalk_pocketCycle.outerCycle
      OsinPocketMultipleEdgeLakeModel.planar).FollowsBoundary

theorem multipleEdgeLakeInnerBranch : MultipleEdgeLakeInnerBranch := by
  refine ⟨?_, OsinPocketMultipleEdgeLakeModel.pocketCycle_innerCycle_followsBoundary,
    OsinPocketMultipleEdgeLakeModel.pocketCycle_outerCycle_not_followsBoundary⟩
  have hb := (OsinPocketMultipleEdgeLakeModel.isNoncrossingClosedWalk_pocketCycle.isBoundaryDart_sideOutside_iff
    OsinPocketMultipleEdgeLakeModel.planar 3).mpr (by decide)
  exact (mem_sideOutside_iff _ _ _).mp hb.1

end OsinPocketCellKeptCellNoncrossing

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.exists_of_noncrossing_of_eitherFollows
#audit_axioms
  GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.exists_kept_of_noncrossingCellWalk_of_value
#audit_axioms
  GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.exists_kept_of_noncrossingCellWalk_of_leastArea
#audit_closed_axioms GroupApproximation.GGT.VanKampen.cellPocketKeptCellNoncrossing
#audit_closed_axioms
  GroupApproximation.GGT.VanKampen.OsinPocketCellKeptCellNoncrossing.multipleEdgeLakeInnerBranch
