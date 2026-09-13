import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94OneCellFace
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundCaseOneFace
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# The X-pocket of Lemma 9.4, Case 1, across one relator cell: the shapes of the pocket walk

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, for a backwards connector pair whose source and
target sides lie across one relator cell `Π` (`OsinLemma94CaseOneSameCellStatement`).  Some
rotation of the face walk reads `X q⁻¹ Y p⁻¹` (`osinLemma94CaseOneWalk_sameCell`), and some
rotation of the carrier of `Π` reads `q B p A`.  In the relator-cell branch `X B` reads an element
other than `1`.  The X-pocket is the side of the closed walk `invDarts X ++ invDarts B`; this module
takes the case where the exterior face is off that side.

Under ruling R1 the loop cut (`nonempty_osinLoopCut_of_pocketRegion`) takes pocket regions whose
two cycles follow their boundary walks.  Their walks are simple
(`PocketRegion.isSimpleClosedWalk_invDarts_outer`), and the side of the complement must have word
norm at most `ε`.  So the X-pocket splits by the shape of its walk:

* `PocketWalkSimpleShape`: no vertex repeats and no dart meets its reverse.  This is the case of the
  loop cut, with side `invDarts X` of norm less than `ε` (`wordNorm_lt_of_end_connector`).
* `PocketWalkFaceBubbleShape`: a vertex repeats on `invDarts X`, a bubble of the face.
* `PocketWalkCellPinchShape`: a vertex repeats on `invDarts B`, a pinch of the carrier of `Π`.
* `PocketWalkTouchVertexShape`: a vertex of `invDarts X` is a vertex of `invDarts B`.  The face
  touches `Π` at a vertex that is not on a side.  Splitting there (`pinchSplit`) gives two lobes
  whose sides are pieces of `X`.  Only the value of `X` is short, so no lobe meets the norm bound
  of the loop cut.
* `PocketWalkSpurShape`: some dart of the walk has its reverse on the walk.

Each shape gives a named statement (`OsinLemma94CaseOneXPocketStatementOf`), and
`osinLemma94CaseOneXPocket_of_shapes` proves the X-pocket statement from the five of them.  None of
`LeastArea`, `DartMinimal` or `Maximal` constrains a vertex touch: they count relator cells, count
darts, and join consecutive sides.  So `OsinLemma94CaseOneTouchVertexStatement` is a genuine leaf.

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

/-! ## The shapes of the pocket walk `x ++ b`, with `x = invDarts X` and `b = invDarts B` -/

section Shapes

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  (Delta : DiscDiagram.{u, w, v} W)

/-- The pocket walk repeats no vertex and meets no dart together with its reverse. -/
abbrev PocketWalkSimpleShape (x b : List Delta.toCombMap.Dart) : Prop :=
  ((x ++ b).map Delta.toCombMap.vertexOf).Nodup ∧
    ∀ d ∈ x ++ b, Delta.toCombMap.alpha d ∉ x ++ b

/-- A vertex repeats on the face part of the pocket walk. -/
abbrev PocketWalkFaceBubbleShape (x _b : List Delta.toCombMap.Dart) : Prop :=
  ¬ (x.map Delta.toCombMap.vertexOf).Nodup

/-- A vertex repeats on the cell part of the pocket walk. -/
abbrev PocketWalkCellPinchShape (_x b : List Delta.toCombMap.Dart) : Prop :=
  ¬ (b.map Delta.toCombMap.vertexOf).Nodup

/-- A vertex of the face part of the pocket walk is a vertex of its cell part. -/
abbrev PocketWalkTouchVertexShape (x b : List Delta.toCombMap.Dart) : Prop :=
  ∃ d ∈ x, ∃ e ∈ b, Delta.toCombMap.vertexOf d = Delta.toCombMap.vertexOf e

/-- Some dart of the pocket walk has its reverse on the walk. -/
abbrev PocketWalkSpurShape (x b : List Delta.toCombMap.Dart) : Prop :=
  ∃ d ∈ x ++ b, Delta.toCombMap.alpha d ∈ x ++ b

end Shapes

/-- **Case 1 of Lemma 9.4 across one relator cell: the X-pocket, under a shape condition.**
The binders of `OsinLemma94CaseOneSameCellStatement`, the face walk data of
`osinLemma94CaseOneWalk_sameCell`, a rotation `q B p A` of the carrier of the cell, `X B` reading
an element other than `1`, the exterior face off the side of `invDarts X ++ invDarts B`, and the
condition `shape` on that walk give `False`. -/
def OsinLemma94CaseOneXPocketStatementOf
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
                            RelLetter.listVal (dartWord S.diagram (X ++ B)) ≠ 1 →
                            S.diagram.outerFace ∉ sideFaces S.diagram.toCombMap
                              (invDarts S.diagram X ++ invDarts S.diagram B) →
                            shape S.diagram (invDarts S.diagram X) (invDarts S.diagram B) →
                            False

/-- **The X-pocket.**  `OsinLemma94CaseOneXPocketStatementOf` with no shape condition. -/
def OsinLemma94CaseOneXPocketStatement : Prop :=
  OsinLemma94CaseOneXPocketStatementOf.{u, w, v} fun _ _ _ => True

/-- **The X-pocket with a simple walk**: the case of the loop cut. -/
def OsinLemma94CaseOneSimplePocketStatement : Prop :=
  OsinLemma94CaseOneXPocketStatementOf.{u, w, v} fun Delta x b => PocketWalkSimpleShape Delta x b

/-- **The X-pocket whose face part repeats a vertex.** -/
def OsinLemma94CaseOneFaceBubbleStatement : Prop :=
  OsinLemma94CaseOneXPocketStatementOf.{u, w, v} fun Delta x b =>
    PocketWalkFaceBubbleShape Delta x b

/-- **The X-pocket whose cell part repeats a vertex.** -/
def OsinLemma94CaseOneCellPinchStatement : Prop :=
  OsinLemma94CaseOneXPocketStatementOf.{u, w, v} fun Delta x b =>
    PocketWalkCellPinchShape Delta x b

/-- **The X-pocket where the face touches the cell at a vertex off the sides.**  The lobes of
`pinchSplit` at the touch have sides that are pieces of `X`, of uncontrolled norm, so the loop cut
does not apply to them as stated. -/
def OsinLemma94CaseOneTouchVertexStatement : Prop :=
  OsinLemma94CaseOneXPocketStatementOf.{u, w, v} fun Delta x b =>
    PocketWalkTouchVertexShape Delta x b

/-- **The X-pocket whose walk meets a dart together with its reverse.** -/
def OsinLemma94CaseOneSpurStatement : Prop :=
  OsinLemma94CaseOneXPocketStatementOf.{u, w, v} fun Delta x b => PocketWalkSpurShape Delta x b

/-- **The X-pocket from its five shapes.**  A pocket walk with no spur, no touch, and no repeated
vertex on either part repeats no vertex at all, so it has the simple shape. -/
theorem osinLemma94CaseOneXPocket_of_shapes
    (hsimple : OsinLemma94CaseOneSimplePocketStatement.{u, w, v})
    (hbubble : OsinLemma94CaseOneFaceBubbleStatement.{u, w, v})
    (hpinch : OsinLemma94CaseOneCellPinchStatement.{u, w, v})
    (htouch : OsinLemma94CaseOneTouchVertexStatement.{u, w, v})
    (hspur : OsinLemma94CaseOneSpurStatement.{u, w, v}) :
    OsinLemma94CaseOneXPocketStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨e1, he1⟩ := hsimple D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨e2, he2⟩ := hbubble D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨e3, he3⟩ := hpinch D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨e4, he4⟩ := htouch D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨e5, he5⟩ := hspur D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨max e1 (max e2 (max e3 (max e4 e5))), fun eps heps => ?_⟩
  obtain ⟨r1, hr1, h1⟩ := he1 eps (by omega)
  obtain ⟨r2, hr2, h2⟩ := he2 eps (by omega)
  obtain ⟨r3, hr3, h3⟩ := he3 eps (by omega)
  obtain ⟨r4, hr4, h4⟩ := he4 eps (by omega)
  obtain ⟨r5, hr5, h5⟩ := he5 eps (by omega)
  refine ⟨max r1 (max r2 (max r3 (max r4 r5))), by omega, fun rho hrho => ?_⟩
  intro W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut hkind j sourceArc
    targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB hout _
  by_cases hsp : PocketWalkSpurShape S.diagram (invDarts S.diagram X) (invDarts S.diagram B)
  · exact h5 rho (by omega) W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut
      hkind j sourceArc targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB hout hsp
  by_cases htv : PocketWalkTouchVertexShape S.diagram (invDarts S.diagram X)
      (invDarts S.diagram B)
  · exact h4 rho (by omega) W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut
      hkind j sourceArc targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB hout htv
  by_cases hbx : ((invDarts S.diagram X).map S.diagram.toCombMap.vertexOf).Nodup
  · by_cases hbb : ((invDarts S.diagram B).map S.diagram.toCombMap.vertexOf).Nodup
    · refine h1 rho (by omega) W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback
        hcut hkind j sourceArc targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB
        hout ⟨?_, fun d hd hmem => hsp ⟨d, hd, hmem⟩⟩
      rw [List.map_append]
      refine List.nodup_append.mpr ⟨hbx, hbb, ?_⟩
      intro a ha a' ha' heq
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha'
      exact htv ⟨d, hd, e, he, heq⟩
    · exact h3 rho (by omega) W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback
        hcut hkind j sourceArc targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB
        hout hbb
  · exact h2 rho (by omega) W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut
      hkind j sourceArc targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB hout hbx

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneXPocket_of_shapes
