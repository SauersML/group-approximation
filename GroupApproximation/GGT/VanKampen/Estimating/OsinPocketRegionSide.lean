import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionInduction
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegion
import GroupApproximation.GGT.VanKampen.SurgeryReclosedVertices
import GroupApproximation.Meta.AxiomGuard

/-!
# The region side of the multiple-edge pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): two distinct selected regions joining the
same two distinct cells `Π_i` and `Π_j` bound a subdiagram `Γ_1` with `∂Γ_1 = s_1 t_1 s_2 t_2`,
where `s_1` and `s_2` are sides of the two regions and `t_1`, `t_2` are arcs of `Π_i` and `Π_j`.
If `Γ_1` kept no relator cell, merging the two regions would contradict the extremality of the
family, so it keeps one.

`MultipleEdgePocketRegionInput` states this region data on the optimal diagram `S.diagram`,
before any collar is inserted:

* a pocket region `P` of `S.diagram` with a relator cell inside and the cells `i`, `j` outside;
* the split `invDarts P.outer.cycle = s₁ ++ invDarts A₁.darts ++ s₂ ++ invDarts A₂.darts`, with
  `A₁` an arc of `Π_i` and `A₂` an arc of `Π_j`.  This is the orientation of
  `ContiguityGeometry.boundary_decomposition`, since `invDarts A.darts` is `A.reverseDarts`;
* sides of length and word norm at most `ε`, with no quasi-geodesic requirement;
* both boundary cycles of `P` follow the face-set boundary.

Consumers.  `OsinMultipleEdgeCut.ofPocketRegion` takes `equiv := S.equiv`, the kept cell as `C`,
and `cell S.diagram i` as `C'` (`cell_mem`).  Under `OsinCCondition` the arc parts are
`(λ, c)`-quasi-geodesic by `isLambdaCQuasiGeodesicWord_invDarts_darts_cellDarts`
(`OsinPocketCellArcs`).  The sides become geodesic only after the separate collar step to an
O-equivalent diagram, which this statement does not presuppose.

Manuscript status: infrastructure for `thm:hull`; certifies no printed sentence on its own.
Stated here, not yet proved.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC Surgery.MapCollapse WordMetric

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The pocket between two regions joining the same two cells** (region side of
`MultipleEdgeCutInput`, before the collar).  Two distinct selected regions joining the distinct
cells `i` and `j` bound a pocket region of the optimal diagram with a relator cell inside and both
cells outside.  The inverse of its complement cycle splits as a side, an arc of `Π_i`, a side and
an arc of `Π_j`, the sides of length and word norm at most `ε`.  Both cycles of the pocket follow
the face-set boundary. -/
def MultipleEdgePocketRegionInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea →
      ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        ∀ a ∈ S.family, ∀ b ∈ S.family, a ≠ b → ∀ i j : Fin S.diagram.rCellCount, i ≠ j →
          a.JoinsCells i j → b.JoinsCells i j →
            ∃ (P : PocketRegion S.diagram)
              (C : RelatorCell S.diagram.toCombMap S.diagram.outerFace W)
              (s₁ s₂ : List S.diagram.toCombMap.Dart)
              (A₁ : CyclicArc (cellDarts S.diagram i)) (A₂ : CyclicArc (cellDarts S.diagram j)),
              C ∈ S.diagram.relatorCells ∧ C.face ∈ P.faces ∧
                (cell S.diagram i).face ∉ P.faces ∧ (cell S.diagram j).face ∉ P.faces ∧
                invDarts S.diagram P.outer.cycle =
                  s₁ ++ invDarts S.diagram A₁.darts ++ s₂ ++ invDarts S.diagram A₂.darts ∧
                s₁.length ≤ eps ∧ s₂.length ≤ eps ∧
                wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord S.diagram s₁)) ≤ eps ∧
                wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord S.diagram s₂)) ≤ eps ∧
                P.inner.FollowsBoundary ∧ P.outer.FollowsBoundary

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.MultipleEdgePocketRegionInput
