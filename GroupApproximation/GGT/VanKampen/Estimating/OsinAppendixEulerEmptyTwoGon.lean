import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegion
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerCount
import GroupApproximation.Meta.AxiomGuard

/-!
# The empty two-gon of `Φ'_M`

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "For any distinguished
system of ε-contiguity subdiagrams `M` in `∆`, the graph `Φ_M` is simple and inside every 2-gon of
`Φ'_M`, there is a vertex of `Φ_M`."  The proof of Lemma 9.7(a) establishes the two-gon half:
"Finally inside every 2-gon `ef` of `Φ'_M` there is a vertex of `Φ_M` since otherwise one can
include the ε-contiguity subdiagrams corresponding to the edges `e` and `f` of `Φ'_M` into a single
ε-contiguity subdiagram in the obvious way, contrary to the definition of `M`."

This module states that merge as a named piece Prop, `EmptyTwoGonInput`, on the carrier
`PocketRegion` (`Estimating/OsinPocketRegion.lean`).  The carrier is the merged region: the faces
of the two regions `a`, `b` together with the pocket between them.  Its boundary is the boundary
of the single ε-contiguity subdiagram of the quote: the merged arc of `∂Π` (reversed), the right
side of `a`, the merged arc of the boundary, and the left side of `b`.  Carrying the merged region
instead of the pocket covers two regions that share a side, where the pocket has no face, and
pinched pockets, where the pocket is not a disc.

The printed merge is `GloballyDistinguishedSectionFamily.false_of_collapse_singleton`
(`Estimating/OsinAppendixCutMerge.lean`) with `absorbed = {a, b}`, against `card_minimal`.
The Euler count `PhiPrimeCountInput` (`Estimating/OsinAppendixEulerCount.lean`) consumes the
Prop at the two-gons of `Φ'_M` whose face holds no relator cell and whose gap at the boundary
holds no corner of the sections.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7(a)); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The empty two-gon of `Φ'_M`** (C6), from the proof of Osin's Lemma 9.7(a): "inside every
2-gon `ef` of `Φ'_M` there is a vertex of `Φ_M` since otherwise one can include the ε-contiguity
subdiagrams corresponding to the edges `e` and `f` of `Φ'_M` into a single ε-contiguity subdiagram
in the obvious way, contrary to the definition of `M`."

Take a least-area diagram, a globally distinguished system `S`, and two different exterior regions
`a`, `b` of the cell `i` to the section `j`.  Take a pocket region `P` of the optimal diagram that
contains the faces of `a` and `b`, no relator cell, and no face of another selected region.  Take
an arc `source` of `∂Π` at least as long as the two source arcs, and an arc `target` of the
boundary from the start of the target arc of `a` to the end of the target arc of `b`, at least as
long as the two target arcs.  If the boundary cycle of the complement of `P`, reversed, is
`source` reversed, the right side of `a`, `target`, and the left side of `b`, there is a
contradiction. -/
def EmptyTwoGonInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea →
      ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        ∀ (i : Fin S.diagram.rCellCount) (j : Fin cuts.count),
          ∀ a ∈ RegionCandidate.exteriorAt S.family i,
            ∀ b ∈ RegionCandidate.exteriorAt S.family i, a ≠ b →
              RegionCandidate.TargetsSectionIndex cuts j a →
                RegionCandidate.TargetsSectionIndex cuts j b →
                  ∀ P : PocketRegion S.diagram, a.1 ⊆ P.faces → b.1 ⊆ P.faces →
                    (∀ C ∈ S.diagram.relatorCells, C.face ∉ P.faces) →
                    (∀ x ∈ S.family, x ≠ a → x ≠ b → Disjoint x.1 P.faces) →
                    ∀ (source : CyclicArc (cellDarts S.diagram i))
                      (target : CyclicArc (targetDarts S.diagram none)),
                      a.2.sourceArc.length + b.2.sourceArc.length ≤ source.length →
                      target.start.1 = a.2.targetArc.start.1 →
                      target.start.1 + target.length =
                        b.2.targetArc.start.1 + b.2.targetArc.length →
                      a.2.targetArc.length + b.2.targetArc.length ≤ target.length →
                      invDarts S.diagram P.outer.cycle =
                        source.reverseDarts ++ a.2.rightSide ++ target.darts ++ b.2.leftSide →
                      False

end GroupApproximation.GGT.VanKampen
