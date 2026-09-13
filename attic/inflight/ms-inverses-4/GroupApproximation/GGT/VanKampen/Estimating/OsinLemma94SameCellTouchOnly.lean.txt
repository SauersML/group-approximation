import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellPocketPinch
import GroupApproximation.Meta.AxiomGuard

/-!
# The X-pocket of Lemma 9.4, Case 1, across one relator cell: a touch-only vertex shape

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, for a backwards connector pair whose source and
target sides lie across one relator cell `Π` (`OsinLemma94CaseOneSameCellStatement`).
`OsinLemma94SameCellPocketPinch` splits the X-pocket by the shape of its walk
`invDarts X ++ invDarts B` into five statements.

`OsinLemma94CaseOneTouchVertexStatement` takes every walk where a vertex of the face part is a vertex
of the cell part.  That condition says nothing about the rest of the walk.  In particular it also
covers walks that carry a spur or a repeated vertex besides the touch, such as a polygon walk
`X = X₁ t X₂ t⁻¹ X₃` around an island of the face (a cutting path `t` taken twice) that touches `Π`.
Refuting those needs the island argument that the spur and face-bubble statements need, so as a leaf
the touch statement contains the open part of those two leaves.

This module states the touch leaf with the rest of the walk clean: a touch, no spur, and no repeated
vertex on either part (`PocketWalkTouchOnlyShape`).  The X-pocket still follows from the five shape
statements with this touch leaf in place of the old one (`osinLemma94CaseOneXPocket_of_touchOnly`):
the case split tests the spur and the two repeated-vertex shapes before the touch.

The touch-only walk is the case of one vertex split.  At a touch vertex `v`, with `x_out`, `b_out`
the walk darts leaving `v` and `x_in`, `b_in` the walk darts entering it, the corners of `f` and of
`Π` at `v` are `σ x_out = alpha x_in` and `σ b_out = alpha b_in`.  So splitting `v` at `alpha x_in`
and `alpha b_in` (`PinchSplit.Input.diagram`) puts the face part and the cell part on different
vertices.  The split keeps every dart, label, relator word and the exterior word, so the side
`invDarts X` keeps its value.

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

section Shapes

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  (Delta : DiscDiagram.{u, w, v} W)

/-- The face part of the pocket walk touches its cell part at a vertex, the walk has no spur, and
neither part repeats a vertex. -/
abbrev PocketWalkTouchOnlyShape (x b : List Delta.toCombMap.Dart) : Prop :=
  PocketWalkTouchVertexShape Delta x b ∧ ¬ PocketWalkSpurShape Delta x b ∧
    (x.map Delta.toCombMap.vertexOf).Nodup ∧ (b.map Delta.toCombMap.vertexOf).Nodup

end Shapes

/-- **The X-pocket where the face touches the cell at a vertex, and the walk is otherwise clean.**
`OsinLemma94CaseOneXPocketStatementOf` under `PocketWalkTouchOnlyShape`. -/
def OsinLemma94CaseOneTouchOnlyStatement : Prop :=
  OsinLemma94CaseOneXPocketStatementOf.{u, w, v} fun Delta x b =>
    PocketWalkTouchOnlyShape Delta x b

/-- The touch statement of `OsinLemma94SameCellPocketPinch` gives the touch-only statement. -/
theorem osinLemma94CaseOneTouchOnly_of_touchVertex
    (htouch : OsinLemma94CaseOneTouchVertexStatement.{u, w, v}) :
    OsinLemma94CaseOneTouchOnlyStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨e, he⟩ := htouch D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨e, fun eps heps => ?_⟩
  obtain ⟨r, hr, h⟩ := he eps heps
  refine ⟨r, hr, fun rho hrho => ?_⟩
  intro W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut hkind j sourceArc
    targetArc X Y r' hj htrav hs ht hsource htarget hX hY n B A hPi hXB hout hshape
  exact h rho hrho W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut hkind j
    sourceArc targetArc X Y r' hj htrav hs ht hsource htarget hX hY n B A hPi hXB hout hshape.1

/-- **The X-pocket from its five shapes, with the touch-only leaf.**  Spurs go to the spur
statement, a repeated vertex on the face part or the cell part to the face-bubble or cell-pinch
statement, a touch of an otherwise clean walk to the touch-only statement, and a walk with none of
these is simple. -/
theorem osinLemma94CaseOneXPocket_of_touchOnly
    (hsimple : OsinLemma94CaseOneSimplePocketStatement.{u, w, v})
    (hbubble : OsinLemma94CaseOneFaceBubbleStatement.{u, w, v})
    (hpinch : OsinLemma94CaseOneCellPinchStatement.{u, w, v})
    (htouch : OsinLemma94CaseOneTouchOnlyStatement.{u, w, v})
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
  by_cases hbx : ((invDarts S.diagram X).map S.diagram.toCombMap.vertexOf).Nodup
  · by_cases hbb : ((invDarts S.diagram B).map S.diagram.toCombMap.vertexOf).Nodup
    · by_cases htv : PocketWalkTouchVertexShape S.diagram (invDarts S.diagram X)
          (invDarts S.diagram B)
      · exact h4 rho (by omega) W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback
          hcut hkind j sourceArc targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB
          hout ⟨htv, hsp, hbx, hbb⟩
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

#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneTouchOnly_of_touchVertex
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneXPocket_of_touchOnly
