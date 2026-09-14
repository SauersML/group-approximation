import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellCellExcisionSides
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellCellLobeWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLoopCutTwoArcs
import GroupApproximation.Meta.AxiomGuard

/-!
# The walk-level X-pocket with a carrier lobe reading `1`: the simple excision

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, across one relator cell `Π`, at walk level
(`OsinLemma94CaseOneXWalkStatementOf`), where the carrier part `invDarts B = l₁ ++ L ++ l₂` has an
innermost lobe `L` reading `1` (`OsinLemma94CaseOneWalkCellLobeExcisionStatement`).  Excising `L`
keeps the value of the pocket walk, and the excised walk `s ++ l₁ ++ l₂` has carrier part the two
arcs `invDarts l₁` and `invDarts l₂` of `Π`.

* `OsinLemma94CaseOneWalkCellLobeExcisionSimpleStatement`: the excised walk is simple and
  `l₁ ++ l₂` is nonempty.  Closed here (`osinLemma94CaseOneWalkCellLobeExcisionSimple`): its pocket
  region holds a relator cell, since the walk reads an element other than `1`.  The two-arc loop
  cut `false_of_pocketRegion_of_below_twoArcs` refutes it below `Δ`, with side `s` of norm less than
  `ε` (the end connector) and the arcs of `SameCellCellLobe.exists_arcs_of_excision`.
* `OsinLemma94CaseOneWalkCellLobeExcisionRestStatement`: the excised walk is not simple, or the lobe
  is the whole carrier part.  Named residual.
* `osinLemma94CaseOneWalkCellLobeExcision_of_simple_rest` and `osinLemma94CaseOneWalkCellPinch_of_rest`:
  the walk-level shape statement rests only on the residual.

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

section Shapes

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  (Delta : DiscDiagram.{u, w, v} W)

/-- An innermost carrier lobe reads `1`, and excising it leaves a simple walk with carrier darts. -/
abbrev PocketWalkCellLobeExcisionSimpleShape (s b : List Delta.toCombMap.Dart) : Prop :=
  ∃ l₁ L l₂ : List Delta.toCombMap.Dart, b = l₁ ++ L ++ l₂ ∧
    IsClosedDartWalk Delta.toCombMap L ∧ (L.map Delta.toCombMap.vertexOf).Nodup ∧
      RelLetter.listVal (dartWord Delta L) = 1 ∧
        IsSimpleClosedWalk Delta.toCombMap (s ++ l₁ ++ l₂) ∧ l₁ ++ l₂ ≠ []

/-- An innermost carrier lobe reads `1`, and excising it leaves a walk that is not simple, or no
carrier darts. -/
abbrev PocketWalkCellLobeExcisionRestShape (s b : List Delta.toCombMap.Dart) : Prop :=
  ∃ l₁ L l₂ : List Delta.toCombMap.Dart, b = l₁ ++ L ++ l₂ ∧
    IsClosedDartWalk Delta.toCombMap L ∧ (L.map Delta.toCombMap.vertexOf).Nodup ∧
      RelLetter.listVal (dartWord Delta L) = 1 ∧
        ¬ (IsSimpleClosedWalk Delta.toCombMap (s ++ l₁ ++ l₂) ∧ l₁ ++ l₂ ≠ [])

end Shapes

/-- **The walk-level X-pocket with a carrier lobe reading `1` whose excision is simple.** -/
def OsinLemma94CaseOneWalkCellLobeExcisionSimpleStatement : Prop :=
  OsinLemma94CaseOneXWalkStatementOf.{u, w, v} fun Delta s b =>
    PocketWalkCellLobeExcisionSimpleShape Delta s b

/-- **The walk-level X-pocket with a carrier lobe reading `1` whose excision is not simple.** -/
def OsinLemma94CaseOneWalkCellLobeExcisionRestStatement : Prop :=
  OsinLemma94CaseOneXWalkStatementOf.{u, w, v} fun Delta s b =>
    PocketWalkCellLobeExcisionRestShape Delta s b

/-- **The excision case from its simple case and the residual.** -/
theorem osinLemma94CaseOneWalkCellLobeExcision_of_simple_rest
    (hsimple : OsinLemma94CaseOneWalkCellLobeExcisionSimpleStatement.{u, w, v})
    (hrest : OsinLemma94CaseOneWalkCellLobeExcisionRestStatement.{u, w, v}) :
    OsinLemma94CaseOneWalkCellLobeExcisionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨e1, he1⟩ := hsimple D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨e2, he2⟩ := hrest D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨max e1 e2, fun eps heps => ?_⟩
  obtain ⟨r1, hr1, h1⟩ := he1 eps (by omega)
  obtain ⟨r2, hr2, h2⟩ := he2 eps (by omega)
  refine ⟨max r1 r2, by omega, fun rho hrho => ?_⟩
  intro W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut hkind j sourceArc
    targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB s hsub hwalk hsval hout
    hshape
  obtain ⟨l₁, L, l₂, hsplit, hL, hnodup, hval⟩ := hshape
  by_cases hsm : IsSimpleClosedWalk S.diagram.toCombMap (s ++ l₁ ++ l₂) ∧ l₁ ++ l₂ ≠ []
  · exact h1 rho (by omega) W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut
      hkind j sourceArc targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB s hsub
      hwalk hsval hout ⟨l₁, L, l₂, hsplit, hL, hnodup, hval, hsm.1, hsm.2⟩
  · exact h2 rho (by omega) W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut
      hkind j sourceArc targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB s hsub
      hwalk hsval hout ⟨l₁, L, l₂, hsplit, hL, hnodup, hval, hsm⟩

namespace SameCellCellLobe

/-- **A carrier lobe reading `1` with a simple excision, refuted below `Δ`.** -/
theorem false_of_walkCellLobe_excision_simple {G : Type u} [Group G] {Lambda : Type w}
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
    (C : WordConnectorPair (symmetricLabelAlphabet D) (P.corner k) (P.word k) (P.sideCount k)
      (P.relatorSides k) (P.longSides k) eps)
    {j : Fin S.diagram.rCellCount} (sourceArc targetArc : CyclicArc (cellDarts S.diagram j))
    {X : List S.diagram.toCombMap.Dart}
    (hX : vertex (P.corner k C.source) (P.word k C.source) C.a' *
        RelLetter.listVal (dartWord S.diagram X) =
      vertex (P.corner k C.target) (P.word k C.target) C.b')
    {n : ℕ} {B A : List S.diagram.toCombMap.Dart}
    (hPi : (cellDarts S.diagram j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A)
    (hXB : RelLetter.listVal (dartWord S.diagram (X ++ B)) ≠ 1)
    {s : List S.diagram.toCombMap.Dart}
    (hsval : RelLetter.listVal (dartWord S.diagram s) =
      RelLetter.listVal (dartWord S.diagram (invDarts S.diagram X)))
    (hout : S.diagram.outerFace ∉ sideFaces S.diagram.toCombMap (s ++ invDarts S.diagram B))
    (hshape : PocketWalkCellLobeExcisionSimpleShape S.diagram s (invDarts S.diagram B)) :
    False := by
  obtain ⟨l₁, L, l₂, hsplit, -, -, hvalL, hw, hne⟩ := hshape
  obtain ⟨A₁, A₂, hA₁, hA₂⟩ := exists_arcs_of_excision sourceArc targetArc hPi hsplit
  have houtM := outerFace_not_mem_sideFaces_excision sourceArc targetArc hPi hsplit hw hne hout
  have hcellM := cell_not_mem_sideFaces_excision sourceArc targetArc hPi hsplit hw hne
  have happ : ∀ a b : List S.diagram.toCombMap.Dart,
      RelLetter.listVal (dartWord S.diagram (a ++ b)) =
        RelLetter.listVal (dartWord S.diagram a) * RelLetter.listVal (dartWord S.diagram b) := by
    intro a b
    simp [Embedded.dartWord, RelLetter.listVal]
  have hvalM : RelLetter.listVal (dartWord S.diagram (s ++ l₁ ++ l₂)) ≠ 1 := by
    rw [listVal_excision_eq hvalL, ← hsplit, happ, hsval, listVal_dartWord_invDarts,
      listVal_dartWord_invDarts, ← mul_inv_rev]
    intro h
    apply hXB
    rw [happ]
    exact mul_eq_one_comm.mp (inv_eq_one.mp h)
  have hnorm : WordMetric.wordNorm D.alphabet.carrier
      (RelLetter.listVal (dartWord S.diagram s)) ≤ eps := by
    rw [hsval, listVal_dartWord_invDarts, WordMetric.wordNorm_inv D.alphabet.symmetricGenerating]
    exact (wordNorm_lt_of_end_connector C hX).le
  have hinv : invDarts S.diagram (PocketRegion.ofSimpleClosedWalk hw houtM).outer.cycle =
      s ++ l₁ ++ l₂ :=
    PocketRegion.ofSimpleClosedWalk_invDarts_outer hw houtM
  have hdecomp : invDarts S.diagram (PocketRegion.ofSimpleClosedWalk hw houtM).outer.cycle =
      s ++ invDarts S.diagram A₁.darts ++ invDarts S.diagram A₂.darts := by
    rw [hinv, ← hA₁, ← hA₂]
  by_cases hcells :
      ∀ Cc ∈ S.diagram.relatorCells, Cc.face ∉ (PocketRegion.ofSimpleClosedWalk hw houtM).faces
  · apply hvalM
    rw [← hinv, listVal_dartWord_invDarts,
      (PocketRegion.ofSimpleClosedWalk hw houtM).listVal_outer_eq_one hcells, inv_one]
  · obtain ⟨C₀, hC₀, hCf⟩ : ∃ Cc ∈ S.diagram.relatorCells,
        Cc.face ∈ (PocketRegion.ofSimpleClosedWalk hw houtM).faces := by
      by_contra hno
      exact hcells fun Cc hCc hmem => hno ⟨Cc, hCc, hmem⟩
    have hi : (cell S.diagram j).face ∉ (PocketRegion.ofSimpleClosedWalk hw houtM).faces := by
      rw [PocketRegion.ofSimpleClosedWalk_faces]
      exact hcellM
    exact false_of_pocketRegion_of_below_twoArcs
      GeodesicCollar.StripStep.geodesicCollarStatement_holds hW hlambda hlambda1 hc hmu hmu1 hrho
      hlarge hleast hbelow S.equiv S.label_admissible (PocketRegion.ofSimpleClosedWalk hw houtM)
      (PocketRegion.ofSimpleClosedWalk_followsBoundary hw houtM).1
      (PocketRegion.ofSimpleClosedWalk_followsBoundary hw houtM).2 hC₀ hCf hi A₁ A₂ s hdecomp
      hnorm

end SameCellCellLobe

open SameCellSimplePocket SameCellCellLobe in
/-- **The walk-level X-pocket with a carrier lobe reading `1` whose excision is simple**, closed. -/
theorem osinLemma94CaseOneWalkCellLobeExcisionSimple :
    OsinLemma94CaseOneWalkCellLobeExcisionSimpleStatement.{u, w, v} := by
  intro G _ Lambda D _hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨0, fun eps _ => ?_⟩
  obtain ⟨rho1, hrho1⟩ := exists_rho_large lambda c hmu eps
  refine ⟨max 1 rho1, by omega, fun rho hrho => ?_⟩
  intro W hW Delta cuts hleast _hpos hbelow S _hcard _hmin P _hmax k C _hback _hcut _hkind j
    sourceArc targetArc X Y r _hj _htrav _hs _ht _hsource _htarget hX _hY n B A hPi hXB s _hsub
    _hwalk hsval hout hshape
  exact false_of_walkCellLobe_excision_simple hW hlambda hlambda1 hc hmu hmu1 (by omega)
    (hrho1 rho (le_of_max_le_right hrho)) hleast hbelow P k C sourceArc targetArc hX hPi hXB
    hsval hout hshape

/-- **The walk-level X-pocket whose carrier part repeats a vertex rests only on the residual.** -/
theorem osinLemma94CaseOneWalkCellPinch_of_rest
    (hrest : OsinLemma94CaseOneWalkCellLobeExcisionRestStatement.{u, w, v}) :
    OsinLemma94CaseOneWalkCellPinchStatement.{u, w, v} :=
  osinLemma94CaseOneWalkCellPinch_of_lobes osinLemma94CaseOneWalkCellLobeValue
    (osinLemma94CaseOneWalkCellLobeExcision_of_simple_rest
      osinLemma94CaseOneWalkCellLobeExcisionSimple hrest)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneWalkCellLobeExcision_of_simple_rest
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellCellLobe.false_of_walkCellLobe_excision_simple
#audit_closed_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneWalkCellLobeExcisionSimple
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneWalkCellPinch_of_rest
