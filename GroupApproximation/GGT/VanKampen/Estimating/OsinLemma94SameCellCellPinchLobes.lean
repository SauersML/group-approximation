import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellPocketPinch
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellPocketWalk
import GroupApproximation.GGT.VanKampen.ClosedWalkInnermostLobe
import GroupApproximation.Meta.AxiomGuard

/-!
# The X-pocket of Lemma 9.4, Case 1, whose cell part repeats a vertex: the two lobe cases

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, across one relator cell `Π`: some rotation of the
face walk reads `X q⁻¹ Y p⁻¹`, some rotation of the carrier of `Π` reads `q B p A`, `X B` reads an
element other than `1`, and the exterior face is off the side of the pocket walk
`invDarts X ++ invDarts B`.  `OsinLemma94CaseOneCellPinchStatement` is the case where the cell
part `invDarts B` repeats a vertex, a pinch of the carrier of `Π`.

The cell part is a walk (`SameCellPocketWalk.exists_window_walks`), so it has an innermost lobe
(`ClosedWalkInnermostLobe.exists_innermost_lobe`): `invDarts B = l₁ ++ L ++ l₂` with `L` a closed
dart walk repeating no vertex.  Every dart of `L` has `Π` across it, so `L` bounds a bubble of `Π`.
The shape statement splits by the value of `L`.

* `OsinLemma94CaseOneCellLobeValueStatement`: `L` reads an element other than `1`.  Then `L` is a
  simple walk `[] ++ invDarts T` for an arc `T` of `Π`, with `Π` off its side, and its bubble holds
  a relator cell.  The walk-level loop-cut kill of the simple case applies with an empty side.
* `OsinLemma94CaseOneCellLobeExcisionStatement`: `L` reads `1`.  Excising it keeps the value of the
  pocket walk, `invDarts X ++ l₁ ++ l₂`, whose cell part consists of the two arcs `invDarts l₂` and
  `invDarts l₁` of `Π`.  This is the case of the two-arc loop cut.
* `osinLemma94CaseOneCellPinch_of_lobes`: the shape statement from the two cases.

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

/-- The cell part of the pocket walk has an innermost lobe reading an element other than `1`. -/
abbrev PocketWalkCellLobeValueShape (_x b : List Delta.toCombMap.Dart) : Prop :=
  ∃ l₁ L l₂ : List Delta.toCombMap.Dart, b = l₁ ++ L ++ l₂ ∧
    IsClosedDartWalk Delta.toCombMap L ∧ (L.map Delta.toCombMap.vertexOf).Nodup ∧
      RelLetter.listVal (dartWord Delta L) ≠ 1

/-- The cell part of the pocket walk has an innermost lobe reading `1`. -/
abbrev PocketWalkCellLobeExcisionShape (_x b : List Delta.toCombMap.Dart) : Prop :=
  ∃ l₁ L l₂ : List Delta.toCombMap.Dart, b = l₁ ++ L ++ l₂ ∧
    IsClosedDartWalk Delta.toCombMap L ∧ (L.map Delta.toCombMap.vertexOf).Nodup ∧
      RelLetter.listVal (dartWord Delta L) = 1

end Shapes

/-- **The X-pocket whose cell part has an innermost lobe reading an element other than `1`.** -/
def OsinLemma94CaseOneCellLobeValueStatement : Prop :=
  OsinLemma94CaseOneXPocketStatementOf.{u, w, v} fun Delta x b =>
    PocketWalkCellLobeValueShape Delta x b

/-- **The X-pocket whose cell part has an innermost lobe reading `1`.** -/
def OsinLemma94CaseOneCellLobeExcisionStatement : Prop :=
  OsinLemma94CaseOneXPocketStatementOf.{u, w, v} fun Delta x b =>
    PocketWalkCellLobeExcisionShape Delta x b

/-- **The X-pocket whose cell part repeats a vertex, from its two lobe cases.**  The cell part is a
walk, so it has an innermost lobe, and that lobe reads `1` or it does not. -/
theorem osinLemma94CaseOneCellPinch_of_lobes
    (hvalue : OsinLemma94CaseOneCellLobeValueStatement.{u, w, v})
    (hexcision : OsinLemma94CaseOneCellLobeExcisionStatement.{u, w, v}) :
    OsinLemma94CaseOneCellPinchStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨e1, he1⟩ := hvalue D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨e2, he2⟩ := hexcision D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨max e1 e2, fun eps heps => ?_⟩
  obtain ⟨r1, hr1, h1⟩ := he1 eps (by omega)
  obtain ⟨r2, hr2, h2⟩ := he2 eps (by omega)
  refine ⟨max r1 r2, by omega, fun rho hrho => ?_⟩
  intro W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut hkind j sourceArc
    targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB hout hpinch
  obtain ⟨_, _, _, _, -, hBwalk, -, -⟩ :=
    SameCellPocketWalk.exists_window_walks sourceArc targetArc htrav hPi hs ht
  have hchain : (invDarts S.diagram B).IsChain fun d e =>
      S.diagram.toCombMap.vertexOf (S.diagram.toCombMap.alpha d) =
        S.diagram.toCombMap.vertexOf e :=
    hBwalk.reverse_map.1
  obtain ⟨l₁, L, l₂, hsplit, hL, hnodup⟩ :=
    ClosedWalkInnermostLobe.exists_innermost_lobe hchain hpinch
  by_cases hval : RelLetter.listVal (dartWord S.diagram L) = 1
  · exact h2 rho (by omega) W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut
      hkind j sourceArc targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB hout
      ⟨l₁, L, l₂, hsplit, hL, hnodup, hval⟩
  · exact h1 rho (by omega) W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut
      hkind j sourceArc targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB hout
      ⟨l₁, L, l₂, hsplit, hL, hnodup, hval⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneCellPinch_of_lobes
