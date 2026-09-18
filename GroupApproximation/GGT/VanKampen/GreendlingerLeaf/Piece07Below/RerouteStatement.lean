import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopyBelow
import GroupApproximation.Manuscript.NonMF.Full.GL03BPinch.Statement
import GroupApproximation.Manuscript.NonMF.Full.GL06e.Refuted
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 07 (below form) rerouted through the corrected enclosed inner pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b); infrastructure for `thm:hull`.
Lane gl-p07-84.

## Why a reroute

`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement` is **FALSE**.  The counterexample is in the
docstring of `GL03BPinch/Statement`: every relator cell sits inside the pocket walk, and the
enclosed face set has a short outer walk, not the two-arc shape.  Every endpoint that takes it as a
hypothesis is vacuous.  The corrected statement `GL03BPinch.InnerPocketEnclosedTwoArcCorrected`
adds a second disjunct: an enclosed face set holding **all** relator cells, with outer walk of
length `≤ ε + ε`.  `GL03BPinch.innerPocketEnclosedTwoArcCorrected` (`GL03BPinch/Endpoint`) proves it.

**LOUD: the second disjunct does not by itself give the proper-arcs conclusion.**  So ONE
residual is needed, and it is already on disk:
`GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement`.  It says that a least-area diagram
below the inductive bound, with long relator words and at least one relator cell, has no enclosed
face set that holds every relator cell and has outer walk of length `≤ ε + ε`.

* It is strictly smaller in proof content than the false statement.  It mentions no pocket walk,
  no contiguity region and no arc decomposition, only a short enclosed boundary.
* It is exactly the configuration of the counterexample, which the false statement mishandled.
* It is true for the same reason as Osin's short-boundary case of Lemma 9.7: under
  `C(ε, μ, λ, c, ρ)` with `ρ` beyond the threshold, no relator cell fits inside a disc bounded by
  `2ε` letters.  The formal route is
  `GL06h3.allCellsShortEnclosedRefutedBelowSection_of_nearestCellCutSection` after
  `GL06h4.nearestCellCutSection_of_pocket`.  It reduces the residual to
  `GL06h4.NearestCellPocketStatement` (the slit pocket at a nearest cell).  No proof of that
  statement is on disk, and this lane did not check it independently.

## Endpoints of this module (none uses the broken `GL03BPinch/Endpoint`)

* `p07Reroute_arcsInput_of_refuted`: the refuted binder (`False`) gives the proper-arcs binder.
* `p07Reroute_arcsInput_of_corrected`: fixed parameters, from `hencl` and the all-cells refutation.
* `p07Reroute_arcs_of_refuted`: `CellPocketWalkProperArcsBelowSectionStatement` from
  `GL06e.CellPocketWalkRefutedBelowSectionStatement`.
* `p07Reroute_arcs_of_corr_allCells`: the target from `hencl` and the all-cells residual.

`Piece07Below/RerouteEndpoint` then plugs in the proved corrected theorem.
`Piece07Below/RerouteFrontier` reroutes the AsmClose live frontier.

## Consumer table

Status names: **R** = rerouted, now needs only the all-cells residual (plus the consumer's own,
unrelated residuals); **D** = dead (vacuous or itself false); **A** = already on the corrected
route.

| consumer of the false statement (file:line) | status |
|---|---|
| `Piece07Below.proof_of_innerPocketEnclosed` (Piece07Below/Proof) | R: `p07Reroute_arcs_allCells` |
| `P07LakeExclusion.proof_of_innerPocketEnclosed` (InnerTwoArcLong) | R: same target |
| `P07LakeExclusion.innerTwoArcLong_of_innerPocketEnclosed` | D: target `InnerTwoArcLong` fails too |
| `AsmFrontier.properArcsBelow_of_innerTwoArcLong` (AsmFrontier/Gaps) | D: through `InnerTwoArcLong` |
| `AsmClose.regionEndpoints_of_liveFrontier` (LiveFrontier:66) | R: `p07Reroute_regionEndpoints` |
| `AsmClose.relativeGreendlinger…Closed_of_liveFrontier` (:78) | R: `p07Reroute_greendlinger` |
| `P06Bypass.refutedBelowSection_of_innerPocketEnclosed` (RefutedCore:97) | R: via `GL06e` |
| `P06Bypass.binderFiveRefutedBelowSection_of_innerPocketEnclosed` (RefutedBridge:45) | R: via `GL06e` |
| `P06Bypass.Waist.refutedBelowSection_of_innerPocketEnclosed_of_long` (WaistInterface:134) | R: via `GL06e` |
| `P06Bypass.relativeGreendlinger…_of_bypassFrontier` (WaistFrontier:61) | R: via `GL06e` |
| `P06Assembly.RefutedOfInnerPocketEnclosedStatement` (Bypass:102) | D: vacuous implication |
| `P06Assembly.greendlinger_of_frontier` (Waist:101) | D: consumes the vacuous one |
| `P06Assembly.proof_of_innerPocketEnclosed_of_bypass` (Proof:70) | D: same |
| producers in P07InnerPocket (Assembly:44,85, LakeReadFixRoute:55, …) | D: target is false |
| `Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea` (GL06/Assembly) | A: see the note below |

The P06Bypass rows are marked R because `GL06e.CellPocketWalkRefutedBelowSectionStatement` has the
same body as `P06Bypass.CellPocketWalkRefutedBelowSectionStatement`.  So
`GL06e.refutedBelowSection_of_innerPocketEnclosedCorrected_of_allCells` supplies their `hrefuted`
binder up to a definitional cast.  No such cast is written here, because the P06Bypass modules are
WIP snapshots that are not registered.  `GL06/Assembly` cites the provisional name
`GL06e.refutedBelowSection_of_innerPocketEnclosedCorrected`.  The name on disk is
`…_of_allCells`, which takes the all-cells residual.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b)).
It certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf

universe u w v

section Input

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **A refuted cell pocket walk binder has proper arcs** (Osin, proof of Lemma 9.7(b)).  The two
binders have the same hypotheses.  The refuted one concludes `False`, so every conclusion follows,
and in particular the proper-arcs one. -/
theorem p07Reroute_arcsInput_of_refuted {D : RelGenSet G Lambda} {lambda c mu : ℝ} {eps : ℕ}
    {W : Set (List (RelLetter G Lambda))}
    (h : GroupApproximation.Full.GL06e.CellPocketWalkRefutedBelowInput.{u, w, v}
      D lambda c mu eps W) :
    CellPocketWalkProperArcsBelowInput.{u, w, v} D lambda c mu eps W := by
  intro Delta cuts hlea hbelow S i j a b ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂
    hw hoff
  exact (h Delta cuts hlea hbelow S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw
    hoff).elim

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.p07Reroute_arcsInput_of_refuted

/-- **Proper arcs at fixed parameters, from the corrected enclosed inner pocket** (Osin, proof of
Lemma 9.7(b); `thm:hull`).  The corrected statement `hencl` and the all-cells refutation `hall`
refute the binder (`GL06e.refutedBelowInput_of_innerPocketEnclosedCorrected`).  The two-arc
disjunct is refuted by `GL06g.false_of_twoArcExit`, the all-cells disjunct by `hall`. -/
theorem p07Reroute_arcsInput_of_corrected
    (hencl : GroupApproximation.Full.GL03BPinch.InnerPocketEnclosedTwoArcCorrected.{u, w, v})
    {D : RelGenSet G Lambda} {W : Set (List (RelLetter G Lambda))} {eps rho : ℕ}
    {mu lambda c : ℝ}
    (hall : GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowInput.{u, w, v}
      D lambda c mu eps W)
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) (hmu : 0 < mu)
    (hmu1 : mu ≤ 1 / 16) (hrho : 2 ≤ rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ)) :
    CellPocketWalkProperArcsBelowInput.{u, w, v} D lambda c mu eps W :=
  p07Reroute_arcsInput_of_refuted
    (GroupApproximation.Full.GL06e.refutedBelowInput_of_innerPocketEnclosedCorrected hencl hall
      hcondition hlambda hlambda1 hc hmu hmu1 hrho hlarge)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.p07Reroute_arcsInput_of_corrected

end Input

/-- **Proper arcs below the inductive bound, beyond thresholds, from the refuted binder** (Osin,
proof of Lemma 9.7(b)).  It uses the same thresholds as the refutation. -/
theorem p07Reroute_arcs_of_refuted
    (h : GroupApproximation.Full.GL06e.CellPocketWalkRefutedBelowSectionStatement.{u, w, v}) :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨eps0, hEps⟩ := h D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hRho⟩ := hEps eps heps
  exact ⟨rho0, hrho0, fun rho hrho W hcondition =>
    p07Reroute_arcsInput_of_refuted (hRho rho hrho W hcondition)⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.p07Reroute_arcs_of_refuted

/-- **Piece 07 (below form), rerouted: proper arcs from the corrected enclosed inner pocket and
the all-cells refutation** (Osin, proof of Lemma 9.7(b); `thm:hull`).  This replaces
`Piece07Below.proof_of_innerPocketEnclosed`, whose hypothesis
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement` is FALSE.  Both hypotheses here are true.
`hencl` is proved as `GL03BPinch.innerPocketEnclosedTwoArcCorrected`.  `hall` is the ONE
remaining residual, see the module docstring. -/
theorem p07Reroute_arcs_of_corr_allCells
    (hencl : GroupApproximation.Full.GL03BPinch.InnerPocketEnclosedTwoArcCorrected.{u, w, v})
    (hall :
      GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v}) :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} :=
  p07Reroute_arcs_of_refuted
    (GroupApproximation.Full.GL06e.refutedBelowSection_of_innerPocketEnclosedCorrected_of_allCells
      hencl hall)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.p07Reroute_arcs_of_corr_allCells

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf
