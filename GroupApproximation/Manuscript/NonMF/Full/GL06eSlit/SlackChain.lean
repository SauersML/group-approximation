import GroupApproximation.Manuscript.NonMF.Full.GL06p.Windows
import GroupApproximation.Manuscript.NonMF.Full.GL06h3.Wired
import GroupApproximation.Manuscript.NonMF.Full.GL06eSlit.Slack
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06e: the GL06p chain for slack slit pocket cores, with the threshold `ε ≥ κ`

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), the all-cells case.  Infrastructure for
`thm:hull` (non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's
Lemma 9.7).

The three GL06p consumers of `slitPocketCoreStatement` are `slitPocketOfNearestPath_of_core`,
`allCellsShort_of_core` and `allCellsShort_of_core_of_gluedWalk`. They use the slit minimality in
one place only: the `omega` step of `longSlitWindows_of_gluedWalk`. With slack `κ` that step gives
a target arc `≤ ε + κ`. `GL06h4.NearWindow` asks for `≤ ε + ε`, so `κ ≤ ε` suffices.

Every threshold on the way to GL06e's residual is existential (`∃ eps0, ∀ eps, eps0 ≤ eps → …`, in
`GL06h3.NearestCellCutSectionStatement` and `GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement`).
So the chain goes through with `eps0 := κ`. The new names:

* `GluedSlitWalkInSlackStatement κ`, `GluedSlitWalkOutSlackStatement κ`: GL06p's glued-walk
  residuals over slack cores. Their content does not involve minimality.
  `gluedSlitWalkIn_of_slack` and `gluedSlitWalkOut_of_slack` give GL06p's exact versions.
* `longSlitWindowsSlackStatement κ` and `longSlitWindowsSlack_of_gluedWalk`: the windows, for
  `κ ≤ ε`.
* `slitPocketOfNearestPathFromStatement eps0`, `shortPocketFromStatement eps0`: GL06p's and
  GL06h4's pocket statements for `eps0 ≤ ε` only.
* `nearestCellCutSection_of_shortPocketFrom`: GL06h3's section statement with threshold `eps0`.
* The three consumers under new names: `slitPocketOfNearestPathFrom_of_slackCore`,
  `allCellsShort_of_slackCore` and `allCellsShort_of_slackCore_of_gluedWalk`.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.GL06eSlit

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.WordMetric

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {κ : ℕ} {Delta : DiscDiagram.{u, w, v} W}

/-- **The slit pocket from a slack core and two windows.** -/
def SlitPocketCoreSlack.toPocket (C : SlitPocketCoreSlack D κ Delta) {eps : ℕ}
    (hin : GL06h4.gl06h4Nearest_NearOrShort D eps C.pocket C.outerPart.length
      (C.outerPart.length + C.slitIn.length))
    (hout : GL06h4.gl06h4Nearest_NearOrShort D eps C.pocket
      (C.outerPart.length + C.slitIn.length + C.arc.length)
      (C.outerPart.length + C.slitIn.length + C.arc.length + C.slitOut.length)) :
    GL06h4.gl06h4Nearest_Pocket D eps Delta where
  copy := C.copy
  equiv := C.equiv
  pocket := C.pocket
  follows := C.follows
  inner := C.inner
  inner_mem := C.inner_mem
  inner_face := C.inner_face
  nearest := C.nearest
  nearest_face := C.nearest_face
  arc := C.arc
  outerPart := C.outerPart
  slitIn := C.slitIn
  slitOut := C.slitOut
  decomposition := C.decomposition
  outer_geodesic := C.outer_geodesic
  slitIn_geodesic := C.slitIn_geodesic
  slitOut_geodesic := C.slitOut_geodesic
  outer_length_le := C.outer_length_le
  near_in := hin
  near_out := hout

end Pocket

/-! ## The glued walks and the windows -/

/-- `GL06p.GluedSlitWalkInStatement` over slack cores. -/
def GluedSlitWalkInSlackStatement (κ : ℕ) : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (C : SlitPocketCoreSlack D κ Delta) (Xi : DiscDiagram.{u, w, v} W),
    OEquivalentDiscDiagram C.pocket.diagram Xi →
      ∀ a : RegionCandidate D eps Xi, a.2.target = none →
        C.outerPart.length ≤ a.2.targetArc.start.1 →
        a.2.targetArc.start.1 + a.2.targetArc.length ≤ C.outerPart.length + C.slitIn.length →
        0 < a.2.sourceArc.length →
          ∃ (Y : DiscDiagram.{u, w, v} W) (_ : Nonempty (OEquivalentDiscDiagram Delta Y))
            (j : Fin Y.rCellCount) (q : List Y.toCombMap.Dart),
            GL06p.IsBoundaryToCellWalk Y j q ∧
              wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord Y q)) ≤
                (a.2.targetArc.start.1 - C.outerPart.length) + eps

/-- `GL06p.GluedSlitWalkOutStatement` over slack cores. -/
def GluedSlitWalkOutSlackStatement (κ : ℕ) : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (C : SlitPocketCoreSlack D κ Delta) (Xi : DiscDiagram.{u, w, v} W),
    OEquivalentDiscDiagram C.pocket.diagram Xi →
      ∀ a : RegionCandidate D eps Xi, a.2.target = none →
        C.outerPart.length + C.slitIn.length + C.arc.length ≤ a.2.targetArc.start.1 →
        a.2.targetArc.start.1 + a.2.targetArc.length ≤
          C.outerPart.length + C.slitIn.length + C.arc.length + C.slitOut.length →
        0 < a.2.sourceArc.length →
          ∃ (Y : DiscDiagram.{u, w, v} W) (_ : Nonempty (OEquivalentDiscDiagram Delta Y))
            (j : Fin Y.rCellCount) (q : List Y.toCombMap.Dart),
            GL06p.IsBoundaryToCellWalk Y j q ∧
              wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord Y q)) ≤
                (C.outerPart.length + C.slitIn.length + C.arc.length + C.slitOut.length -
                  (a.2.targetArc.start.1 + a.2.targetArc.length)) + eps

/-- The slack glued walk gives GL06p's exact one: an exact core is a slack core. -/
theorem gluedSlitWalkIn_of_slack (κ : ℕ) (h : GluedSlitWalkInSlackStatement.{u, w, v} κ) :
    GL06p.GluedSlitWalkInStatement.{u, w, v} := by
  intro _G _ _Lambda D eps W Delta C Xi E a hnone hlo hhi hsrc
  exact h D eps W Delta (SlitPocketCoreSlack.ofCore κ C) Xi E a hnone hlo hhi hsrc

/-- The slack glued walk gives GL06p's exact one: an exact core is a slack core. -/
theorem gluedSlitWalkOut_of_slack (κ : ℕ) (h : GluedSlitWalkOutSlackStatement.{u, w, v} κ) :
    GL06p.GluedSlitWalkOutStatement.{u, w, v} := by
  intro _G _ _Lambda D eps W Delta C Xi E a hnone hlo hhi hsrc
  exact h D eps W Delta (SlitPocketCoreSlack.ofCore κ C) Xi E a hnone hlo hhi hsrc

/-- **The windows on long slit sides of a slack core, for `κ ≤ ε`** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121). -/
def longSlitWindowsSlackStatement (κ : ℕ) : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W), κ ≤ eps →
    Delta.LeastArea → (∀ d, (symmetricLabelAlphabet D).IsLetter (Delta.label d)) →
      (∀ word ∈ W, 1 < word.length) → 2 ≤ Delta.rCellCount →
        Delta.boundaryWord.length ≤ eps + eps →
          ∀ C : SlitPocketCoreSlack D κ Delta,
            (eps + eps < C.slitIn.length →
              GL06h4.NearWindow D eps C.pocket C.outerPart.length
                (C.outerPart.length + C.slitIn.length)) ∧
            (eps + eps < C.slitOut.length →
              GL06h4.NearWindow D eps C.pocket
                (C.outerPart.length + C.slitIn.length + C.arc.length)
                (C.outerPart.length + C.slitIn.length + C.arc.length + C.slitOut.length))

/-- **The windows from the glued walks, with slack** (Osin, proof of Lemma 9.7(b)): as
`GL06p.longSlitWindows_of_gluedWalk`; the target arc is at most `ε + κ ≤ ε + ε`. -/
theorem longSlitWindowsSlack_of_gluedWalk (κ : ℕ)
    (hin : GluedSlitWalkInSlackStatement.{u, w, v} κ)
    (hout : GluedSlitWalkOutSlackStatement.{u, w, v} κ) :
    longSlitWindowsSlackStatement.{u, w, v} κ := by
  intro _G _ _Lambda D eps W Delta hκ _hlea _hletters _hW _hcells _hboundary C
  refine ⟨fun _hlong => ?_, fun _hlong => ?_⟩
  · intro Xi E a hnone hlo hhi hsrc
    obtain ⟨Y, hY, j, q, hq, hnorm⟩ := hin D eps W Delta C Xi E a hnone hlo hhi hsrc
    have hmin := C.slitIn_minimal Y hY j q hq
    omega
  · intro Xi E a hnone hlo hhi hsrc
    obtain ⟨Y, hY, j, q, hq, hnorm⟩ := hout D eps W Delta C Xi E a hnone hlo hhi hsrc
    have hmin := C.slitOut_minimal Y hY j q hq
    omega

/-! ## The pocket statements beyond a threshold -/

/-- `GL06p.slitPocketOfNearestPathStatement` for `eps0 ≤ ε` only. -/
def slitPocketOfNearestPathFromStatement (eps0 : ℕ) : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W), eps0 ≤ eps →
    Delta.LeastArea → (∀ d, (symmetricLabelAlphabet D).IsLetter (Delta.label d)) →
      (∀ word ∈ W, 1 < word.length) → 2 ≤ Delta.rCellCount →
        Delta.boundaryWord.length ≤ eps + eps →
          GL06p.NearestCellPath Delta →
            Nonempty (GL06h4.gl06h4Nearest_Pocket D eps Delta)

/-- `GL06h4.gl06h4Nearest_shortPocketStatement` for `eps0 ≤ ε` only. -/
def shortPocketFromStatement (eps0 : ℕ) : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W), eps0 ≤ eps →
    Delta.LeastArea → (∀ d, (symmetricLabelAlphabet D).IsLetter (Delta.label d)) →
      (∀ word ∈ W, 1 < word.length) → 2 ≤ Delta.rCellCount →
        Delta.boundaryWord.length ≤ eps + eps →
          Nonempty (GL06h4.gl06h4Nearest_Pocket D eps Delta)

/-- **Consumer 1, slack version** (`GL06p.slitPocketOfNearestPath_of_core`): the slit pocket of
a nearest path from a slack core and the slack windows, for `κ ≤ ε`. -/
theorem slitPocketOfNearestPathFrom_of_slackCore (κ : ℕ)
    (hcore : slitPocketCoreSlackStatement.{u, w, v} κ)
    (hwin : longSlitWindowsSlackStatement.{u, w, v} κ) :
    slitPocketOfNearestPathFromStatement.{u, w, v} κ := by
  intro _G _ _Lambda D eps W Delta hκ hlea hletters hW hcells hboundary _N
  obtain ⟨M⟩ := GL06p.exists_metricNearestWalk D Delta (by omega)
  obtain ⟨C⟩ := hcore D W Delta hlea hletters hW hcells M
  obtain ⟨hin, hout⟩ := hwin D eps W Delta hκ hlea hletters hW hcells hboundary C
  refine ⟨C.toPocket ?_ ?_⟩
  · by_cases h : C.slitIn.length ≤ eps + eps
    · exact GL06p.nearOrShort_of_le D eps C.pocket _ _ h
    · exact Or.inr (hin (by omega))
  · by_cases h : C.slitOut.length ≤ eps + eps
    · exact GL06p.nearOrShort_of_le D eps C.pocket _ _ h
    · exact Or.inr (hout (by omega))

/-- A nearest cell and a minimal path always exist. -/
theorem shortPocketFrom_of_slitPocketOfNearestPathFrom (eps0 : ℕ)
    (h : slitPocketOfNearestPathFromStatement.{u, w, v} eps0) :
    shortPocketFromStatement.{u, w, v} eps0 := by
  intro _G _ _Lambda D eps W Delta heps hlea hletters hW hcells hboundary
  exact h D eps W Delta heps hlea hletters hW hcells hboundary
    (GL06p.exists_nearestCellPath Delta (by omega)).some

/-- The nearest-cell cut at a fixed `ε ≥ eps0`, as
`GL06h4.gl06h4Nearest_nearestCellCutInput_of_shortPocket`. -/
theorem nearestCellCutInput_of_shortPocketFrom {eps0 : ℕ}
    (h : shortPocketFromStatement.{u, w, v} eps0)
    {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps : ℕ} (heps : eps0 ≤ eps)
    {rho : ℕ} {mu lambda c : ℝ} (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) :
    GL06h3.NearestCellCutInput.{u, w, v} D lambda c eps W := by
  intro Xi hlea hletters hW hcells hboundary
  obtain ⟨N⟩ := h D eps W Xi heps hlea hletters hW hcells hboundary
  exact ⟨Xi, hlea, rfl, ⟨(GL06h4.gl06h4Nearest_toNearestCellPocket N).toNearestCellCut hcondition
    hlambda1 hc hlea hboundary⟩⟩

/-- **The nearest-cell cut beyond the threshold `eps0`.** -/
theorem nearestCellCutSection_of_shortPocketFrom (eps0 : ℕ)
    (h : shortPocketFromStatement.{u, w, v} eps0) :
    GL06h3.NearestCellCutSectionStatement.{u, w, v} := by
  intro _G _ _Lambda D _hhyp lambda c _mu _hlambda hlambda1 hc _hmu _hmu1
  refine ⟨eps0, fun _eps heps => ⟨1, Nat.one_pos, fun _rho _hrho _W hcondition => ?_⟩⟩
  exact nearestCellCutInput_of_shortPocketFrom h heps hcondition hlambda1 hc

/-- **Consumer 2, slack version** (`GL06p.allCellsShort_of_core`): GL06e's all-cells residual from
a slack core and the slack windows. -/
theorem allCellsShort_of_slackCore (κ : ℕ) (hcore : slitPocketCoreSlackStatement.{u, w, v} κ)
    (hwin : longSlitWindowsSlackStatement.{u, w, v} κ) :
    GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v} :=
  GL06h3.allCellsShortEnclosedRefutedBelowSection_of_nearestCellCutSection
    (nearestCellCutSection_of_shortPocketFrom κ
      (shortPocketFrom_of_slitPocketOfNearestPathFrom κ
        (slitPocketOfNearestPathFrom_of_slackCore κ hcore hwin)))

/-- **Consumer 3, slack version** (`GL06p.allCellsShort_of_core_of_gluedWalk`): GL06e's all-cells
residual from a slack core and the slack glued walks. -/
theorem allCellsShort_of_slackCore_of_gluedWalk (κ : ℕ)
    (hcore : slitPocketCoreSlackStatement.{u, w, v} κ)
    (hin : GluedSlitWalkInSlackStatement.{u, w, v} κ)
    (hout : GluedSlitWalkOutSlackStatement.{u, w, v} κ) :
    GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v} :=
  allCellsShort_of_slackCore κ hcore (longSlitWindowsSlack_of_gluedWalk κ hin hout)

end GroupApproximation.Full.GL06eSlit

#audit_axioms GroupApproximation.Full.GL06eSlit.gluedSlitWalkIn_of_slack
#audit_axioms GroupApproximation.Full.GL06eSlit.gluedSlitWalkOut_of_slack
#audit_axioms GroupApproximation.Full.GL06eSlit.longSlitWindowsSlack_of_gluedWalk
#audit_axioms GroupApproximation.Full.GL06eSlit.slitPocketOfNearestPathFrom_of_slackCore
#audit_axioms GroupApproximation.Full.GL06eSlit.nearestCellCutSection_of_shortPocketFrom
#audit_axioms GroupApproximation.Full.GL06eSlit.allCellsShort_of_slackCore
#audit_axioms GroupApproximation.Full.GL06eSlit.allCellsShort_of_slackCore_of_gluedWalk
