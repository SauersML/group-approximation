import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellCellLobeSides
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellCellPinchLobes
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellSimplePocket
import GroupApproximation.Meta.AxiomGuard

/-!
# The X-pocket of Lemma 9.4, Case 1, whose carrier part has a lobe reading an element other than `1`

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, across one relator cell `Π`, with the exterior face
off the side of the pocket walk `invDarts X ++ invDarts B`, and an innermost lobe `L` of the carrier
part `invDarts B` (`PocketWalkCellLobeValueShape`) reading an element other than `1`.

`L` is a simple walk (`SameCellCellLobe.isSimpleClosedWalk_lobe`) and reads `[] ++ invDarts T` for
an arc `T` of `Π` (`SameCellCellLobe.exists_arc_of_lobe`).  `Π` is off its side, and so is the
exterior face (`SameCellCellLobe.cell_not_mem_sideFaces_lobe`,
`SameCellCellLobe.outerFace_not_mem_sideFaces_lobe`).  The walk-level loop-cut kill
`SameCellSimplePocket.false_of_simpleWalk_of_below` then applies with an empty side, whose value has
word norm `0`.

* `SameCellCellLobe.false_of_cellLobe_value`: the refutation for one configuration.
* `osinLemma94CaseOneCellLobeValue : OsinLemma94CaseOneCellLobeValueStatement`, closed.

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
open GroupApproximation.GGT.VanKampen.CaseOneWalk

namespace SameCellCellLobe

/-- **A lobe of the carrier part reading an element other than `1`, refuted below `Δ`.** -/
theorem false_of_cellLobe_value {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps rho : ℕ}
    {mu lambda c : ℝ} (hW : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 < lambda)
    (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) (hmu : 0 < mu) (hmu1 : mu ≤ 1 / 16) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (hleast : Delta.LeastArea)
    (hbelow : ∀ (Xi : DiscDiagram.{u, w, v} W) (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
      Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
        ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi, OsinLemma97bConclusion mu T)
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    {j : Fin S.diagram.rCellCount} (sourceArc targetArc : CyclicArc (cellDarts S.diagram j))
    {X Y : List S.diagram.toCombMap.Dart} {r : ℕ}
    (htrav : (S.diagram.faceBoundary (P.face k)).darts.rotate r =
      X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts)
    (hs : 0 < sourceArc.length)
    {n : ℕ} {B A : List S.diagram.toCombMap.Dart}
    (hPi : (cellDarts S.diagram j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A)
    (hout : S.diagram.outerFace ∉ sideFaces S.diagram.toCombMap
      (invDarts S.diagram X ++ invDarts S.diagram B))
    (hshape : PocketWalkCellLobeValueShape S.diagram (invDarts S.diagram X)
      (invDarts S.diagram B)) :
    False := by
  obtain ⟨l₁, L, l₂, hsplit, hL, hnodup, hval⟩ := hshape
  have hw := isSimpleClosedWalk_lobe hL hnodup hval
  obtain ⟨T, hT⟩ := exists_arc_of_lobe sourceArc targetArc hPi hsplit
  have hnorm : WordMetric.wordNorm D.alphabet.carrier
      (RelLetter.listVal (dartWord S.diagram ([] : List S.diagram.toCombMap.Dart))) ≤ eps := by
    have h1 : RelLetter.listVal (dartWord S.diagram ([] : List S.diagram.toCombMap.Dart)) = 1 := by
      simp [Embedded.dartWord, RelLetter.listVal]
    rw [h1, WordMetric.wordNorm_one]
    exact Nat.zero_le _
  exact SameCellSimplePocket.false_of_simpleWalk_of_below hW hlambda hlambda1 hc hmu hmu1 hrho
    hlarge hleast hbelow S.equiv S.label_admissible hw
    (outerFace_not_mem_sideFaces_lobe (P.face_not_cell k j) sourceArc targetArc htrav hPi hs
      hsplit hw hout)
    (cell_not_mem_sideFaces_lobe sourceArc targetArc hPi hsplit hw) T hT hnorm hval

end SameCellCellLobe

open SameCellSimplePocket SameCellCellLobe in
/-- **The X-pocket whose carrier part has a lobe reading an element other than `1`**, closed. -/
theorem osinLemma94CaseOneCellLobeValue :
    OsinLemma94CaseOneCellLobeValueStatement.{u, w, v} := by
  intro G _ Lambda D _hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨0, fun eps _ => ?_⟩
  obtain ⟨rho1, hrho1⟩ := exists_rho_large lambda c hmu eps
  refine ⟨max 1 rho1, by omega, fun rho hrho => ?_⟩
  intro W hW Delta cuts hleast _hpos hbelow S _hcard _hmin P _hmax k _C _hback _hcut _hkind j
    sourceArc targetArc X Y r _hj htrav hs _ht _hsource _htarget _hX _hY n B A hPi _hXB hout
    hshape
  exact false_of_cellLobe_value hW hlambda hlambda1 hc hmu hmu1 (by omega)
    (hrho1 rho (le_of_max_le_right hrho)) hleast hbelow P k sourceArc targetArc htrav hs hPi hout
    hshape

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.SameCellCellLobe.false_of_cellLobe_value
#audit_closed_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneCellLobeValue
