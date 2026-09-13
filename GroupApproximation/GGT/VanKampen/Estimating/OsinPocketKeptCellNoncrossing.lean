import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketKeptCellAbsorbed
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionNoncrossingWalk
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkEuler
import GroupApproximation.Meta.AxiomGuard

/-!
# The kept cell of a noncrossing pocket walk

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of
`Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

`GloballyDistinguishedSectionFamily.exists_kept_of_pocketRegion_of_value` gives a relator cell in
any pocket region whose cycle is the pocket walk.  The walk can touch itself at a vertex, and
`PocketRegion.ofNoncrossingClosedWalk` builds the region from four inputs.  Two of them are proved
here for the pocket walk.

* `PocketWalk.outerFace_not_mem_sideFaces_of_noncrossing`: the exterior face is off the side of a
  noncrossing pocket walk, since a dart of the target arc is a walk dart whose reversal lies on the
  exterior face.  This is the input `hout`.
* The Euler equality `heuler` is `IsNoncrossingClosedWalk.reclosed_euler` (lane hull-euler), once
  the outer cycle follows its boundary.
* `GloballyDistinguishedSectionFamily.exists_kept_of_noncrossing_of_value`, and the named
  proposition `PocketKeptCellNoncrossingStatement` with its proof `pocketKeptCellNoncrossing`: a
  relator cell lies on the side of the walk.  The two remaining inputs are hypotheses: the walk is
  noncrossing (`hw`), and its outer cycle follows its boundary (`hfollows`).  Lane hull-select
  produces both from first turns (`Estimating/OsinPocketFirstTurnWalk.lean`).

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7); certifies no printed sentence
on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

namespace PocketWalk

variable {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The exterior face is off the side of a noncrossing pocket walk.**  A dart of the target arc
is a walk dart, and its reversal lies on the exterior face, so the face across it is off the side
of the walk. -/
theorem outerFace_not_mem_sideFaces_of_noncrossing (K : PocketWalk D eps X lo hi)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk) :
    X.outerFace ∉ sideFaces X.toCombMap K.walk := by
  obtain ⟨d, hd⟩ := K.targetArc.exists_mem_darts K.targetArc_pos
  have hdw : d ∈ K.walk := by
    show d ∈ K.firstSide ++ invDarts X K.sourceArc.darts ++ K.secondSide ++ K.targetArc.darts
    exact List.mem_append_right _ hd
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp (K.targetArc.mem_cycle_of_mem_darts hd)
  have hface : X.toCombMap.faceOf e = X.outerFace :=
    ((X.faceBoundary X.outerFace).mem_iff e).mp (List.mem_reverse.mp he)
  have h := And.right ((hw.isBoundaryDart_sideFaces_iff X.planar _).mpr hdw)
  rwa [X.toCombMap.alpha_involutive e, hface] at h

end PocketWalk

namespace GloballyDistinguishedSectionFamily

variable {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The kept cell of a noncrossing pocket walk.**  Let `x ≠ y` be selected regions and `K` a
pocket walk to section `j` whose source arc spans those of `x`, a gap and `y`, whose first side is
the left side of `y` and whose second side is the right side of `x`.  If no relator word has value
one, the walk is noncrossing and its outer cycle follows its boundary, then a relator cell lies on
the side of the walk.  The pocket region is `PocketRegion.ofNoncrossingClosedWalk`, with the
exterior face off the side from the target arc and the Euler equality from `reclosed_euler`. -/
theorem exists_kept_of_noncrossing_of_value
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {j : Fin cuts.count} {x y : RegionCandidate D eps S.diagram}
    (hxS : x ∈ S.family) (hyS : y ∈ S.family) (hxy : x ≠ y)
    (K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ))
    (hgap : ∃ Gap : CyclicArc (cellDarts S.diagram i),
      K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts)
    (hfirst : K.firstSide = y.2.leftSide) (hsecond : K.secondSide = x.2.rightSide)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hw : IsNoncrossingClosedWalk S.diagram.toCombMap K.walk)
    (hfollows : (hw.outerCycle S.diagram.planar).FollowsBoundary) :
    ∃ kept : Fin S.diagram.rCellCount,
      (cell S.diagram kept).face ∈ sideFaces S.diagram.toCombMap K.walk := by
  have hout := K.outerFace_not_mem_sideFaces_of_noncrossing hw
  have heuler := hw.reclosed_euler S.diagram.planar hfollows
  obtain ⟨kept, hkept⟩ := S.exists_kept_of_pocketRegion_of_value hxS hyS hxy K hgap hfirst
    hsecond hvalue (PocketRegion.ofNoncrossingClosedWalk hw hout hfollows heuler)
    (PocketRegion.ofNoncrossingClosedWalk_inner_cycle hw hout hfollows heuler)
  rw [PocketRegion.ofNoncrossingClosedWalk_faces] at hkept
  exact ⟨kept, hkept⟩

end GloballyDistinguishedSectionFamily

/-- **The kept cell of a noncrossing pocket walk**, as a named proposition.  For a globally
distinguished section family, selected regions `x ≠ y`, and a pocket walk `K` to section `j` whose
source arc spans those of `x`, a gap and `y`, whose first side is the left side of `y` and whose
second side is the right side of `x`: if no relator word has value one, the walk is noncrossing and
its outer cycle follows its boundary, then a relator cell lies on the side of the walk. -/
def PocketKeptCellNoncrossingStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (i : Fin S.diagram.rCellCount) (j : Fin cuts.count) (x y : RegionCandidate D eps S.diagram),
    x ∈ S.family → y ∈ S.family → x ≠ y →
      ∀ K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ),
        (∃ Gap : CyclicArc (cellDarts S.diagram i),
          K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts) →
        K.firstSide = y.2.leftSide → K.secondSide = x.2.rightSide →
        (∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) →
        ∀ hw : IsNoncrossingClosedWalk S.diagram.toCombMap K.walk,
          (hw.outerCycle S.diagram.planar).FollowsBoundary →
            ∃ kept : Fin S.diagram.rCellCount,
              (cell S.diagram kept).face ∈ sideFaces S.diagram.toCombMap K.walk

theorem pocketKeptCellNoncrossing : PocketKeptCellNoncrossingStatement.{u, w, v} := by
  intro _ _ _ _ _ _ _ _ _ _ S _ _ _ _ hxS hyS hxy K hgap hfirst hsecond hvalue hw hfollows
  exact GloballyDistinguishedSectionFamily.exists_kept_of_noncrossing_of_value S hxS hyS hxy K
    hgap hfirst hsecond hvalue hw hfollows

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.outerFace_not_mem_sideFaces_of_noncrossing
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.exists_kept_of_noncrossing_of_value
#audit_closed_axioms GroupApproximation.GGT.VanKampen.pocketKeptCellNoncrossing
