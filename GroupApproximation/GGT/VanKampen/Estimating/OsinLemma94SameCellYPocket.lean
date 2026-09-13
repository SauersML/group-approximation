import Mathlib.Data.List.Rotate
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellPocketPinch
import GroupApproximation.Meta.AxiomGuard

/-!
# The Y-pocket of Lemma 9.4, Case 1, across one relator cell, from the X-pocket

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, for a backwards connector pair whose source and
target sides lie across one relator cell `Π` (`OsinLemma94CaseOneSameCellStatement`).  Some
rotation of the face walk reads `X q⁻¹ Y p⁻¹` (`osinLemma94CaseOneWalk_sameCell`), and some
rotation of the carrier of `Π` reads `q B p A`.  The pocket walks are `invDarts X ++ invDarts B`
and `invDarts Y ++ invDarts A`.  `OsinLemma94SameCellPocketPinch` states the X-pocket under five
shape conditions and reduces it to them.  This module states the Y-pocket and derives it from the
X-pocket, shape by shape.

## The symmetry

Swap the source and target of the connector pair (`WordConnectorPair.swapBackward`): the new source
segment is `[b', b]`, the new target segment is `[a', a]`, and the two geodesic connectors trade
places.  The backward hypothesis `b' < b` becomes the forward clause of the new pair, and the old
forward clause `a < a'` becomes its backward hypothesis.  The side-set memberships of the new pair
hold because both sides are arcs of `Π`: a cell side is a relator side and a long side.

The face walk `X q⁻¹ Y p⁻¹`, rotated by the length of `X q⁻¹`, reads `Y p⁻¹ X q⁻¹`.  The carrier
`q B p A`, rotated by the length of `q B`, reads `p A q B`.  So the data of the Y-pocket of the pair
are the data of the X-pocket of the swapped pair, with `X := Y` and `B := A`, and the shape
condition is on the same walk.

* `WordConnectorPair.swapBackward`: the swapped pair.
* `OsinLemma94CaseOneYPocketStatementOf shape` and `OsinLemma94CaseOneYPocketStatement`.
* `osinLemma94CaseOneYPocketOf_of_xPocketOf`: each X-pocket shape statement gives the Y-pocket
  statement of the same shape.
* `osinLemma94CaseOneYPocket_of_shapes`: the Y-pocket from the same five shape statements.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.4, Case 1).  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

namespace UnboundEstimate.WordConnectorPair

variable {G : Type u} [Group G] {Lambda : Type w} {D : RelGenSet G Lambda} {v : ℕ → G}
  {word : ℕ → List (RelLetter G Lambda)} {n eps : ℕ} {A B : Set ℕ}

/-- **The connector pair with source and target swapped.**  For a backwards pair (`b' < b`) whose
target lies in the source set and whose source lies in the target set, the target segment
`[b', b]` read forwards is a source segment, the source segment `[a', a]` is a target segment, and
the end and start connectors trade places. -/
def swapBackward (C : WordConnectorPair D v word n A B eps) (hback : C.b' < C.b)
    (hA : C.target ∈ A) (hB : C.source ∈ B) : WordConnectorPair D v word n A B eps where
  source := C.target
  target := C.source
  source_lt := C.target_lt
  target_lt := C.source_lt
  source_mem := hA
  target_mem := hB
  distinct := C.distinct.symm
  source_admissible := C.target_admissible
  target_admissible := C.source_admissible
  a := C.b'
  a' := C.b
  b := C.a'
  b' := C.a
  a_le := C.b'_le
  a'_le := C.b_le
  b_le := C.a'_le
  b'_le := C.a_le
  source_forward := hback
  source_long := by
    rw [GroupApproximation.WordMetric.wordDist_comm D.alphabet.symmetricGenerating]
    exact C.target_long
  target_long := by
    rw [GroupApproximation.WordMetric.wordDist_comm D.alphabet.symmetricGenerating]
    exact C.source_long
  startConnector := C.endConnector
  endConnector := C.startConnector
  start_geodesic := C.end_geodesic
  end_geodesic := C.start_geodesic
  start_short := C.end_short
  end_short := C.start_short

end UnboundEstimate.WordConnectorPair

/-- **Case 1 of Lemma 9.4 across one relator cell: the Y-pocket, under a shape condition.**
The binders of `OsinLemma94CaseOneSameCellStatement`, the face walk data of
`osinLemma94CaseOneWalk_sameCell`, a rotation `q B p A` of the carrier of the cell, `Y A` reading
an element other than `1`, the exterior face off the side of `invDarts Y ++ invDarts A`, and the
condition `shape` on that walk give `False`. -/
def OsinLemma94CaseOneYPocketStatementOf
    (shape : ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
      (Delta : DiscDiagram.{u, w, v} W), List Delta.toCombMap.Dart → List Delta.toCombMap.Dart →
        Prop) : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              (∀ (Xi : DiscDiagram.{u, w, v} W)
                  (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
                Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
                  ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi,
                    OsinLemma97bConclusion mu T) →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal →
                    ∀ (k : Fin P.count) (C : WordConnectorPair (symmetricLabelAlphabet D)
                      (P.corner k) (P.word k) (P.sideCount k) (P.relatorSides k)
                      (P.longSides k) eps),
                      C.b' < C.b → P.kind k C.target ≠ .cutting →
                        P.kind k C.source = P.kind k C.target →
                        ∀ (j : Fin S.diagram.rCellCount)
                          (sourceArc targetArc : CyclicArc (cellDarts S.diagram j))
                          (X Y : List S.diagram.toCombMap.Dart) (r : ℕ),
                          P.kind k C.source = .cell j →
                          (S.diagram.faceBoundary (P.face k)).darts.rotate r =
                            X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts →
                          0 < sourceArc.length → 0 < targetArc.length →
                          vertex (P.corner k C.source) (P.word k C.source) C.a *
                              RelLetter.listVal (dartWord S.diagram sourceArc.reverseDarts) =
                            vertex (P.corner k C.source) (P.word k C.source) C.a' →
                          vertex (P.corner k C.target) (P.word k C.target) C.b' *
                              RelLetter.listVal (dartWord S.diagram targetArc.reverseDarts) =
                            vertex (P.corner k C.target) (P.word k C.target) C.b →
                          vertex (P.corner k C.source) (P.word k C.source) C.a' *
                              RelLetter.listVal (dartWord S.diagram X) =
                            vertex (P.corner k C.target) (P.word k C.target) C.b' →
                          vertex (P.corner k C.target) (P.word k C.target) C.b *
                              RelLetter.listVal (dartWord S.diagram Y) =
                            vertex (P.corner k C.source) (P.word k C.source) C.a →
                          ∀ (n : ℕ) (B A : List S.diagram.toCombMap.Dart),
                            (cellDarts S.diagram j).rotate n =
                              targetArc.darts ++ B ++ sourceArc.darts ++ A →
                            RelLetter.listVal (dartWord S.diagram (Y ++ A)) ≠ 1 →
                            S.diagram.outerFace ∉ sideFaces S.diagram.toCombMap
                              (invDarts S.diagram Y ++ invDarts S.diagram A) →
                            shape S.diagram (invDarts S.diagram Y) (invDarts S.diagram A) →
                            False

/-- **The Y-pocket.**  `OsinLemma94CaseOneYPocketStatementOf` with no shape condition. -/
def OsinLemma94CaseOneYPocketStatement : Prop :=
  OsinLemma94CaseOneYPocketStatementOf.{u, w, v} fun _ _ _ => True

/-- **The Y-pocket of a pair is the X-pocket of the swapped pair**, for every shape condition. -/
theorem osinLemma94CaseOneYPocketOf_of_xPocketOf
    (shape : ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
      (Delta : DiscDiagram.{u, w, v} W), List Delta.toCombMap.Dart → List Delta.toCombMap.Dart →
        Prop)
    (h : OsinLemma94CaseOneXPocketStatementOf.{u, w, v} shape) :
    OsinLemma94CaseOneYPocketStatementOf.{u, w, v} shape := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨e0, he0⟩ := h D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨e0, fun eps heps => ?_⟩
  obtain ⟨r0, hr0, hr⟩ := he0 eps heps
  refine ⟨r0, hr0, fun rho hrho => ?_⟩
  intro W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut hkind j sourceArc
    targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hYA hout hshape
  have hA : C.target ∈ P.relatorSides k :=
    show ∃ j' : Fin S.diagram.rCellCount, P.kind k C.target = .cell j' from
      ⟨j, hkind.symm.trans hj⟩
  have hB : C.source ∈ P.longSides k :=
    show P.kind k C.source ≠ .short from fun hshort => by cases hj.symm.trans hshort
  have hcut' : P.kind k C.source ≠ .cutting := by
    rw [hkind]
    exact hcut
  have htrav' : (S.diagram.faceBoundary (P.face k)).darts.rotate
      (r + (X ++ targetArc.reverseDarts).length) =
        Y ++ sourceArc.reverseDarts ++ X ++ targetArc.reverseDarts := by
    rw [← List.rotate_rotate, htrav]
    simpa only [List.append_assoc] using
      List.rotate_append_length_eq (X ++ targetArc.reverseDarts) (Y ++ sourceArc.reverseDarts)
  have hPi' : (cellDarts S.diagram j).rotate (n + (targetArc.darts ++ B).length) =
      sourceArc.darts ++ A ++ targetArc.darts ++ B := by
    rw [← List.rotate_rotate, hPi]
    simpa only [List.append_assoc] using
      List.rotate_append_length_eq (targetArc.darts ++ B) (sourceArc.darts ++ A)
  exact hr rho hrho W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k
    (C.swapBackward hback hA hB) C.source_forward hcut' hkind.symm j targetArc sourceArc Y X
    (r + (X ++ targetArc.reverseDarts).length) (hkind.symm.trans hj) htrav' ht hs htarget hsource
    hY hX (n + (targetArc.darts ++ B).length) A B hPi' hYA hout hshape

/-- **The Y-pocket from the five X shape statements.** -/
theorem osinLemma94CaseOneYPocket_of_shapes
    (hsimple : OsinLemma94CaseOneSimplePocketStatement.{u, w, v})
    (hbubble : OsinLemma94CaseOneFaceBubbleStatement.{u, w, v})
    (hpinch : OsinLemma94CaseOneCellPinchStatement.{u, w, v})
    (htouch : OsinLemma94CaseOneTouchVertexStatement.{u, w, v})
    (hspur : OsinLemma94CaseOneSpurStatement.{u, w, v}) :
    OsinLemma94CaseOneYPocketStatement.{u, w, v} :=
  osinLemma94CaseOneYPocketOf_of_xPocketOf (fun _ _ _ => True)
    (osinLemma94CaseOneXPocket_of_shapes hsimple hbubble hpinch htouch hspur)

/-- **Both pockets from the five X shape statements.** -/
theorem osinLemma94CaseOnePockets_of_shapes
    (hsimple : OsinLemma94CaseOneSimplePocketStatement.{u, w, v})
    (hbubble : OsinLemma94CaseOneFaceBubbleStatement.{u, w, v})
    (hpinch : OsinLemma94CaseOneCellPinchStatement.{u, w, v})
    (htouch : OsinLemma94CaseOneTouchVertexStatement.{u, w, v})
    (hspur : OsinLemma94CaseOneSpurStatement.{u, w, v}) :
    OsinLemma94CaseOneXPocketStatement.{u, w, v} ∧ OsinLemma94CaseOneYPocketStatement.{u, w, v} :=
  ⟨osinLemma94CaseOneXPocket_of_shapes hsimple hbubble hpinch htouch hspur,
    osinLemma94CaseOneYPocket_of_shapes hsimple hbubble hpinch htouch hspur⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.WordConnectorPair.swapBackward
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneYPocketOf_of_xPocketOf
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneYPocket_of_shapes
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOnePockets_of_shapes
