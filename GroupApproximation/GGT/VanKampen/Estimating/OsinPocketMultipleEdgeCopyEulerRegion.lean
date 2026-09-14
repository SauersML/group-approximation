import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopyOrderEuler
import GroupApproximation.Meta.AxiomGuard

/-!
# The multiple-edge pocket region from the Euler equalities, without a pinch

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(a): the subdiagram `Ξ` between two distinguished
`ε`-contiguity subdiagrams joining the same two cells, with `∂Ξ = s_1 t_1 s_2 t_2`.

`OsinPocketMultipleEdgeCopyOrderEuler` and `OsinPocketMultipleEdgeCopyOrderSection` build the
binder-5 region data on a copy through the cell pinch, whose simple copy makes both cycles of the
pocket follow their boundaries.  The component-route transports of lane w1-binder-6 take least area
in place of following, so a cut builder over them only needs the pocket region.  This module
builds that region directly from the walk with the exterior off its side, with no pinch and no
proper arcs.
* The Euler equalities of `CellPocketWalkEulerStatement` make
  `PocketRegion.ofNoncrossingClosedWalkEuler` a pocket region whose cycle is the walk.
* `exists_kept_of_cellPocketRegion_of_leastArea` puts a relator cell inside it.
* `CellPocketWalk.toCellPocketFaceSetOfNoncrossing` keeps both cells outside.
* The inverse complement cycle is the walk `s_1 t_1⁻¹ s_2 t_2⁻¹`.

* `MultipleEdgePocketRegionEulerCopyInput`: the region data of `MultipleEdgePocketRegionCopyInput`
  without the two following conjuncts; `MultipleEdgePocketRegionCopyInput.toEuler`.
* `copyRegionEuler_of_offSideWalk` and `multipleEdgePocketRegionEulerCopyInput_of_order`: the
  producer from the clean copy in both orders, the exterior off the side in some order and the Euler
  residual.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(a));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides

section Input

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The multiple-edge pocket region on an O-equivalent copy, without following cycles.**  As
`MultipleEdgePocketRegionCopyInput`, without `P.inner.FollowsBoundary ∧ P.outer.FollowsBoundary`. -/
def MultipleEdgePocketRegionEulerCopyInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
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
                  wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X s₂)) ≤ eps

/-- The region data with following cycles gives the region data without. -/
theorem MultipleEdgePocketRegionCopyInput.toEuler {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    (h : MultipleEdgePocketRegionCopyInput.{u, w, v} D lambda c eps W) :
    MultipleEdgePocketRegionEulerCopyInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S a ha b hb hab i j hij hai hbi
  obtain ⟨X, hE, hlabel, P, C, i', j', s₁, s₂, A₁, A₂, hC, hCf, hi, hj, hdec, hn₁, hn₂, -, -⟩ :=
    h Delta cuts hlea S a ha b hb hab i j hij hai hbi
  exact ⟨X, hE, hlabel, P, C, i', j', s₁, s₂, A₁, A₂, hC, hCf, hi, hj, hdec, hn₁, hn₂⟩

end Input

section Order

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The region data from one walk with the exterior off its side, from the Euler equalities.**  For
distinct selected regions `a`, `b` of an optimal family joining the distinct cells `i`, `j` under the
edge conditions, a cell pocket walk with the walk data of the order `(a, b)` and the closed-walk facts,
whose side does not hold the exterior, gives the region data on the optimal diagram: the Euler pocket
region of the walk. -/
theorem copyRegionEuler_of_offSideWalk
    (heuler : CellPocketWalkEulerStatement.{u, w, v})
    {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (hlea : Delta.LeastArea) (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ S.family) (hb : b ∈ S.family) (hab : a ≠ b) (hij : i ≠ j)
    (hai : a.JoinsCells i j) (hbi : b.JoinsCells i j) (hclean : CellPocketWalk.CopyClean a b i j)
    (K : CellPocketWalk D eps S.diagram i j)
    (hfirst : K.firstSide = b.sideFrom j) (hsecond : K.secondSide = a.sideFrom i)
    (h₁ : ∃ G₁ : CyclicArc (cellDarts S.diagram i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (h₂ : ∃ G₂ : CyclicArc (cellDarts S.diagram j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    (hne : K.walk ≠ [])
    (hchain : K.walk.IsChain fun d e => S.diagram.toCombMap.vertexOf
      (S.diagram.toCombMap.alpha d) = S.diagram.toCombMap.vertexOf e)
    (hcloses : S.diagram.toCombMap.vertexOf (S.diagram.toCombMap.alpha (K.walk.getLast hne)) =
      S.diagram.toCombMap.vertexOf (K.walk.head hne))
    (hnodup : K.walk.Nodup) (halpha : ∀ d ∈ K.walk, S.diagram.toCombMap.alpha d ∉ K.walk)
    (hoff : S.diagram.outerFace ∉ sideFaces S.diagram.toCombMap K.walk) :
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
          wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X s₂)) ≤ eps := by
  have horient : ∀ faces : Finset S.diagram.toCombMap.Face,
      (∀ d, ¬ (S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ faces ↔
        S.diagram.toCombMap.faceOf d ∈ faces) ↔ walkKeep S.diagram.toCombMap K.walk d) →
      ∀ d ∈ K.walk, ∀ e ∈ K.walk,
        (S.diagram.toCombMap.faceOf d ∈ faces ↔ S.diagram.toCombMap.faceOf e ∈ faces) :=
    fun _ hcol => CellPocketWalkColour.walk_orient S.toRealizedSectionFamily ha hb hab hai hbi K
      hfirst hsecond h₁ h₂ hcol
  have hw : IsNoncrossingClosedWalk S.diagram.toCombMap K.walk :=
    ClosedWalkFaceColouring.isNoncrossingClosedWalk_of_orient S.diagram.planar hne hnodup halpha
      hchain hcloses horient
  have hlea' : S.diagram.LeastArea := S.equiv.leastArea hlea
  obtain ⟨hinner, houter⟩ := heuler hlea S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw
  obtain ⟨kept, hkept⟩ : ∃ kept : Fin S.diagram.rCellCount,
      (cell S.diagram kept).face ∈ sideFaces S.diagram.toCombMap K.walk :=
    S.exists_kept_of_cellPocketRegion_of_leastArea ha hb hab hij hai hbi K hfirst hsecond h₁ hlea'
      (PocketRegion.ofNoncrossingClosedWalkEuler hw hoff hinner houter) rfl
  have hfirstOut : (cell S.diagram i).face ∉ sideFaces S.diagram.toCombMap K.walk :=
    (K.toCellPocketFaceSetOfNoncrossing kept hw hoff hkept).first_not_mem
  have hsecondOut : (cell S.diagram j).face ∉ sideFaces S.diagram.toCombMap K.walk :=
    (K.toCellPocketFaceSetOfNoncrossing kept hw hoff hkept).second_not_mem
  exact ⟨S.diagram, ⟨S.equiv⟩, fun d => S.label_admissible d,
    PocketRegion.ofNoncrossingClosedWalkEuler hw hoff hinner houter, cell S.diagram kept, i, j,
    K.firstSide, K.secondSide, K.firstArc, K.secondArc, cell_mem S.diagram kept, hkept, hfirstOut,
    hsecondOut, PocketRegion.invDarts_reverse_map_alpha K.walk, K.firstSide_norm_le,
    K.secondSide_norm_le⟩

/-- **The multiple-edge pocket region on a copy, through the chosen order, from the Euler
equalities**, at fixed parameters: the clean family in both orders, both walks with their closed-walk
facts, the walk with the exterior off its side, and its Euler pocket region. -/
theorem multipleEdgePocketRegionEulerCopyInput_of_order
    (hcopy : CellPocketCopyCleanBothOrdersStatement.{u, w, v})
    (hout : CellPocketWalkOuterOffSideSomeOrderStatement.{u, w, v})
    (heuler : CellPocketWalkEulerStatement.{u, w, v})
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} :
    MultipleEdgePocketRegionEulerCopyInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S a ha b hb hab i j hij hai hbi
  obtain ⟨S', a', b', i', j', ha', hb', hab', hij', hai', hbi', hclean₁, hclean₂⟩ :=
    hcopy D lambda c eps W Delta cuts hlea S a ha b hb hab i j hij hai hbi
  have hlea' : S'.diagram.LeastArea := S'.equiv.leastArea hlea
  obtain ⟨K₁, hf₁, hs₁, hA₁, hB₁, hne₁, hch₁, hcl₁⟩ :=
    CellPocketWalk.exists_of_joinsCells_closedWalk S'.toRealizedSectionFamily ha' hb' hab' hij'
      hai' hbi'
  obtain ⟨hnd₁, hal₁⟩ := K₁.walk_nodup_and_alpha_not_mem hlea' hij' hf₁ hs₁
    (S'.pairwise a' ha' b' hb' hab') hclean₁
  obtain ⟨K₂, hf₂, hs₂, hA₂, hB₂, hne₂, hch₂, hcl₂⟩ :=
    CellPocketWalk.exists_of_joinsCells_closedWalk S'.toRealizedSectionFamily hb' ha' hab'.symm
      hij' hbi' hai'
  obtain ⟨hnd₂, hal₂⟩ := K₂.walk_nodup_and_alpha_not_mem hlea' hij' hf₂ hs₂
    (S'.pairwise b' hb' a' ha' hab'.symm) hclean₂
  rcases hout S'.toRealizedSectionFamily ha' hb' hab' hij' hai' hbi' K₁ K₂ hf₁ hs₁ hA₁ hB₁ hne₁
      hch₁ hcl₁ hnd₁ hal₁ hf₂ hs₂ hA₂ hB₂ hne₂ hch₂ hcl₂ hnd₂ hal₂ with hoff | hoff
  · exact copyRegionEuler_of_offSideWalk heuler hlea S' ha' hb' hab' hij' hai' hbi' hclean₁ K₁
      hf₁ hs₁ hA₁ hB₁ hne₁ hch₁ hcl₁ hnd₁ hal₁ hoff
  · exact copyRegionEuler_of_offSideWalk heuler hlea S' hb' ha' hab'.symm hij' hbi' hai' hclean₂
      K₂ hf₂ hs₂ hA₂ hB₂ hne₂ hch₂ hcl₂ hnd₂ hal₂ hoff

end Order

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.MultipleEdgePocketRegionEulerCopyInput
#audit_axioms GroupApproximation.GGT.VanKampen.MultipleEdgePocketRegionCopyInput.toEuler
#audit_axioms GroupApproximation.GGT.VanKampen.copyRegionEuler_of_offSideWalk
#audit_axioms GroupApproximation.GGT.VanKampen.multipleEdgePocketRegionEulerCopyInput_of_order
