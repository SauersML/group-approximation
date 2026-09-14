import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionInduction
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegion
import GroupApproximation.GGT.VanKampen.SurgeryReclosedVertices
import GroupApproximation.GGT.VanKampen.SymmetricLabelAlphabet
import GroupApproximation.Meta.AxiomGuard

/-!
# The region side of the multiple-edge pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): two distinct selected regions joining the
same two distinct cells `Π_i` and `Π_j` bound a subdiagram `Γ_1` with `∂Γ_1 = s_1 t_1 s_2 t_2`,
where `s_1` and `s_2` are sides of the two regions and `t_1`, `t_2` are arcs of `Π_i` and `Π_j`.
If `Γ_1` kept no relator cell, merging the two regions would contradict the extremality of the
family, so it keeps one.

`MultipleEdgePocketRegionInput` states this region data on an O-equivalent copy `X` of the
least-area diagram with labels in the symmetric label alphabet (ruling (B)), before any collar is
inserted:

* a pocket region `P` of `X` with a relator cell inside and two cells `i'`, `j'` of `X` outside;
* the split `invDarts P.outer.cycle = s₁ ++ invDarts A₁.darts ++ s₂ ++ invDarts A₂.darts`, with
  `A₁` an arc of `Π_{i'}` and `A₂` an arc of `Π_{j'}`.  This is the orientation of
  `ContiguityGeometry.boundary_decomposition`, since `invDarts A.darts` is `A.reverseDarts`;
* sides of word norm at most `ε`, with no length or quasi-geodesic requirement;
* both boundary cycles of `P` follow the face-set boundary.

Consumer.  `multipleEdgeCutInput_of_pieces` (OsinPocketMultipleEdgeAssembly) inserts a collar of
geodesic words along both sides and composes the equivalences.  Under `OsinCCondition` the arc
parts are `(λ, c)`-quasi-geodesic by `isLambdaCQuasiGeodesicWord_invDarts_darts_cellDarts`
(`OsinPocketCellArcs`); the sides become geodesic only after the collar.

Manuscript status: infrastructure for `thm:hull`; certifies no printed sentence on its own.
Stated here, not yet proved.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC Surgery.MapCollapse WordMetric

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The pocket between two regions joining the same two cells** (region side of
`MultipleEdgeCutInput`, before the collar).  Two distinct selected regions joining the distinct
cells `i` and `j` give an O-equivalent copy of the least-area diagram with labels in the symmetric
label alphabet, and a pocket region of the copy with a relator cell inside and two cells outside.
The inverse of its complement cycle splits as a side, an arc of the first cell, a side and an arc
of the second, the sides of word norm at most `ε`.  Both cycles of the pocket follow the face-set
boundary. -/
def MultipleEdgePocketRegionInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea →
      ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        ∀ a ∈ S.family, ∀ b ∈ S.family, a ≠ b → ∀ i j : Fin S.diagram.rCellCount, i ≠ j →
          a.JoinsCells i j → b.JoinsCells i j →
            ∃ X : DiscDiagram.{u, w, v} W, Nonempty (OEquivalentDiscDiagram Delta X) ∧
              (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) ∧
              ∃ (P : PocketRegion X) (C : RelatorCell X.toCombMap X.outerFace W)
                (i' j' : Fin X.rCellCount) (s₁ s₂ : List X.toCombMap.Dart)
                (A₁ : CyclicArc (cellDarts X i')) (A₂ : CyclicArc (cellDarts X j')),
                C ∈ X.relatorCells ∧ C.face ∈ P.faces ∧
                  (cell X i').face ∉ P.faces ∧ (cell X j').face ∉ P.faces ∧
                  invDarts X P.outer.cycle =
                    s₁ ++ invDarts X A₁.darts ++ s₂ ++ invDarts X A₂.darts ∧
                  wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X s₁)) ≤ eps ∧
                  wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X s₂)) ≤ eps ∧
                  P.inner.FollowsBoundary ∧ P.outer.FollowsBoundary

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.MultipleEdgePocketRegionInput
