import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PlanarPieces

/-!
# Case 1 of Osin's Lemma 9.4: the face walk around a backwards connector pair

In Case 1 of the proof of Osin's Appendix Lemma 9.4 (arXiv:math/0411039v3), the two connectors
`s_1`, `s_2` of a pair (39) cut a quadrilateral `q_1 s_1 q_2^{-1} s_2` out of a component
polygon.  Here a polygon is an unselected `G`-face of the optimal diagram
(`OsinLemma94RealizedPolygons`), and the connector pair joins the segment `[a, a']` of an (A1)
side to the segment `[b', b]` of an (A1) or (A2) side, with `b' < b`.

`OsinLemma94CaseOneWalkStatement` records the walk of that face as the surgery of
`GFaceWordInsertion.exists_quadrilateral_region` consumes it.  Some rotation of the walk reads
`X ++ T ++ Y ++ P`:
* `P` is the source segment, the reversed darts of a nonempty arc of a relator cell;
* `X` runs from the corner after the source segment to the corner before the target segment;
* `T` is the target segment, an arc of a relator cell read from across, or an arc of `∂Δ`
  inside one section;
* `Y` runs from the corner after the target segment back to the source segment.

The values of `X` and `Y` are the values the connectors `s_1` (`endConnector`) and `s_2`
(`startConnector`) carry between the same corners.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents

/-- **The quadrilateral on the face walk.**  For a backwards connector pair of polygon `k`
whose target side is not a cutting path, some rotation of the face walk reads
`X ++ T ++ Y ++ P`, where `P` reverses a nonempty relator-cell arc (the source segment
`[a, a']`), `T` is the nonempty target segment `[b', b]` as a region boundary reads it (inside
one section when it lies on `∂Δ`), and `X`, `Y` join the corners of the two segments with the
values of the corners they join. -/
def OsinLemma94CaseOneWalkStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    (C : WordConnectorPair D (P.corner k) (P.word k) (P.sideCount k) (P.relatorSides k)
      (P.longSides k) eps),
    C.b' < C.b → P.kind k C.target ≠ .cutting →
      ∃ (source : Fin S.diagram.rCellCount) (target : Option (Fin S.diagram.rCellCount))
        (sourceArc : CyclicArc (cellDarts S.diagram source))
        (targetArc : CyclicArc (targetDarts S.diagram target))
        (X Y : List S.diagram.toCombMap.Dart) (r : ℕ),
        (S.diagram.faceBoundary (P.face k)).darts.rotate r =
            X ++ targetBoundaryDarts S.diagram target targetArc ++ Y ++
              sourceArc.reverseDarts ∧
          0 < sourceArc.length ∧ 0 < targetArc.length ∧
          (target = none → ∃ j : Fin cuts.count,
            cuts.cut j.castSucc ≤ targetArc.start.val ∧
              targetArc.start.val + targetArc.length ≤ cuts.cut j.succ) ∧
          vertex (P.corner k C.source) (P.word k C.source) C.a' *
              RelLetter.listVal (dartWord S.diagram X) =
            vertex (P.corner k C.target) (P.word k C.target) C.b' ∧
          vertex (P.corner k C.target) (P.word k C.target) C.b *
              RelLetter.listVal (dartWord S.diagram Y) =
            vertex (P.corner k C.source) (P.word k C.source) C.a

end GroupApproximation.GGT.VanKampen
