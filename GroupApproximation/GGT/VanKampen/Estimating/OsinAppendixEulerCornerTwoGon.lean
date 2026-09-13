import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerExteriorTwoGon
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSections
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionDarts
import GroupApproximation.Meta.AxiomGuard

/-!
# The two-gons of `Φ'_M` whose gap at the outer vertex holds a corner

Osin, arXiv:math/0411039v3, Appendix, proof of Lemma 9.3: "By (∗), every region of it (except
possibly for the outer one) has degree at least three".  With one merged outer vertex `O`
(`Estimating/OsinAppendixEulerExterior.lean`), a face of `phiMapO` of degree less than six is a
two-gon between two different exterior regions of one cell (`exterior_of_isTwoGon`).  Its dart `y`
at `O` carries a region `a`, and two steps on around the face lies the other region `b`.  At `O`
the retained darts follow the outer boundary, so the target arcs of `a` and `b` are consecutive
along `∂Δ`.  The stretch of `∂Δ` after the target arc of `a` and before the target arc of `b` is
the gap of the two-gon at `O`.

This module states C4 of the plan in `notes/nm-swarm/reports/hull-euler.md` as a named piece Prop:

* `RegionCandidate.GapHoldsCorner cuts a b k`: the cut `cuts.cut k` lies on the stretch from the
  end of the target arc of `a` to the start of the target arc of `b`, read forwards and
  cyclically;
* `RegionCandidate.GapAtOHoldsCorner cuts family E f`: the face `f` of `phiMapO family E` has a
  dart at `O` whose gap holds a corner;
* `CornerTwoGonInput`: at most `r` two-gons of `phiMapO` have a corner in their gap at `O`.

The count holds because the target arcs are nonempty, pairwise disjoint and inside one section
each (`RespectsSections`), so different two-gons at `O` have disjoint gaps and a corner lies in at
most one gap.  A two-gon with no corner in its gap has both regions to one section, `a` before
`b`, which is the situation of `EmptyTwoGonInput` (`Estimating/OsinAppendixEulerEmptyTwoGon.lean`).

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7(a)); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

variable {G : Type u} [Group G] {Lambda : Type w}

namespace Embedded.RegionCandidate

variable {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W} {lambda c : ℝ} {word : List (RelLetter G Lambda)}

/-- **Corner `k` lies in the gap after `a`**: the cut `cuts.cut k` lies on the stretch of the
boundary from the end of the target arc of `a` to the start of the target arc of `b`, read forwards
and cyclically.  A stretch through the base point holds the corner `0`. -/
def GapHoldsCorner (cuts : SectionCuts D lambda c word) (a b : RegionCandidate D eps Delta)
    (k : Fin cuts.count) : Prop :=
  if a.2.targetArc.start.1 + a.2.targetArc.length ≤ b.2.targetArc.start.1 then
    a.2.targetArc.start.1 + a.2.targetArc.length ≤ cuts.cut k.castSucc ∧
      cuts.cut k.castSucc ≤ b.2.targetArc.start.1
  else
    a.2.targetArc.start.1 + a.2.targetArc.length ≤ cuts.cut k.castSucc ∨
      cuts.cut k.castSucc ≤ b.2.targetArc.start.1

/-- **The gap at the outer vertex of a face of `Φ'_M` holds a corner**: the face has a dart `y` at
the outer vertex, and some corner lies in the gap after the region of `y` and before the region two
steps on around the face. -/
def GapAtOHoldsCorner (cuts : SectionCuts D lambda c word)
    (family E : Finset (RegionCandidate D eps Delta)) (f : (phiMapO family E).Face) : Prop :=
  ∃ y : (phiMapO family E).Dart, (phiMapO family E).faceOf y = f ∧ phiCellSideO y = true ∧
    sideCellO (phiRegionO y) (phiSideO y) = none ∧
      ∃ k : Fin cuts.count, GapHoldsCorner cuts (phiRegionO y)
        (phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))) k

end Embedded.RegionCandidate

open scoped Classical in
/-- **The two-gons of `Φ'_M` whose gap at the outer vertex holds a corner** (C4 of Lemma 9.3).
Take a globally distinguished system `S` and a set `E` of its regions carrying `ExtPhiData`.  At
most `r = cuts.count` two-gons of `phiMapO S.family E` have a corner in their gap at `O`. -/
def CornerTwoGonInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (E : Finset (RegionCandidate D eps S.diagram)) (P : RegionCandidate.ExtPhiData S.family E),
      (Finset.univ.filter fun f : (RegionCandidate.phiMapO S.family E).Face =>
          (RegionCandidate.phiSubdividedMultigraphO P).IsTwoGon f ∧
            RegionCandidate.GapAtOHoldsCorner cuts S.family E f).card ≤ cuts.count

end GroupApproximation.GGT.VanKampen
