import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchOuterDispatch
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.Proof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 10 (live): the case assembly and the non-rose bridge

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  `PocketOuterPinchStepSectionStatement` (`Estimating/OsinPocketPinchOuterDispatch`)
is the `hstep` residual of `relativeGreendlingerQuasiGeodesicLeastArea_of_eightResiduals`
(`GreendlingerLeaf/Common/EightResidualWaist`).

This module replaces `GreendlingerLeaf/Piece10/Proof` (lane gl-p10-03).  It never imports
`Piece10/Proof` or `P10Rose/Proof` (the dead filter route), and it does not define a second
`NonRoseStepStatement`: the non-rose case is `P10ChordLift.NonRoseStepStatement`, closed
unconditionally by `P10ChordLift.proof` (`GreendlingerLeaf/P10ChordLift/Proof`).  The declaration names
`Piece10.proof_of_cases` and `Piece10.proof_of_rose` collide intentionally with the module
`Piece10/Proof`; the two must never be imported together.

## Route

A case split on the rose configuration `P10ChordLift.AllNonFirstTurnsCrossed K`
(`GreendlingerLeaf/P10ChordLift/Predicate`), at the larger of the two thresholds for `ε` and for `ρ`.

* Some non-first turn is not crossed: `P10ChordLift.proof`.
* Every non-first turn is crossed: the rose case `P10ChordLift.RoseStepStatement`.

* `proof_of_cases`: the step from the two cases.
* `proof_of_rose`: the step from the rose case alone (non-rose case closed by `P10ChordLift.proof`).
* `RoseReductionStatement`, `proof_of_roseReduction`: the rose-side interface of lane gl-p10-02.

## Interface of lane gl-p10-02 (not on disk at authoring time)

The live rose reduction module `GreendlingerLeaf/P10Rose/Live/Reduction` (lane gl-p10-02) provides
`P10Rose.rose_of_regionMoveSubArc : RoseRegionMoveSubArcStatement.{u, w, v} →
P10ChordLift.RoseStepStatement.{u, w, v}` and `P10Rose.rose_of_inPlaceStep :
RoseInPlaceStepStatement.{u, w, v} → P10ChordLift.RoseStepStatement.{u, w, v}`.  At authoring time
only `Live/Reduction/InPlace` existed (used by `Piece10Live/InPlace` for `proof_of_inPlaceStep`), so
this module does not import that chain and states the shape of such a reduction as
`RoseReductionStatement Gap := Gap → P10ChordLift.RoseStepStatement` and proves
`proof_of_roseReduction`.  Once the sub-arc module of `Live/Reduction` lands, the lane endpoints
are, in a module importing both this one and `Live/Reduction` (the second one is already on disk
in `Piece10Live/InPlace`, in the direct form `proof_of_rose (P10Rose.rose_of_inPlaceStep h)`):

```
theorem proof_of_regionMoveSubArc (h : P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  proof_of_roseReduction (Gap := P10Rose.RoseRegionMoveSubArcStatement.{u, w, v})
    P10Rose.rose_of_regionMoveSubArc h
theorem proof_of_inPlaceStep (h : P10Rose.RoseInPlaceStepStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  proof_of_roseReduction (Gap := P10Rose.RoseInPlaceStepStatement.{u, w, v})
    P10Rose.rose_of_inPlaceStep h
```

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10

universe u w v

/-- **The outer-pinch step from its two cases**, at the larger of the two thresholds for `ε` and for
`ρ`: split on whether every non-first turn of the boundary cycle is crossed. -/
theorem proof_of_cases (hnon : P10ChordLift.NonRoseStepStatement.{u, w, v})
    (hrose : P10ChordLift.RoseStepStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} := by
  intro _ _ _ D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := hnon D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps1, heps1⟩ := hrose D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max eps0 eps1, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps ((le_max_left eps0 eps1).trans heps)
  obtain ⟨rho1, -, hrho1⟩ := heps1 eps ((le_max_right eps0 eps1).trans heps)
  refine ⟨max rho0 rho1, lt_of_lt_of_le hrho0 (le_max_left rho0 rho1),
    fun rho hrho' W hcondition => ?_⟩
  intro X lo hi hlea hlabel K hK hturns hprop htgt hpinch
  by_cases hall : P10ChordLift.AllNonFirstTurnsCrossed K
  · exact hrho1 rho ((le_max_right rho0 rho1).trans hrho') W hcondition X lo hi hlea hlabel K hK
      hturns hprop htgt hpinch hall
  · exact hrho rho ((le_max_left rho0 rho1).trans hrho') W hcondition X lo hi hlea hlabel K hK
      hturns hprop htgt hpinch hall

/-- **The outer-pinch step from the rose case**: the non-rose case is closed unconditionally by the
chord lift endpoint `P10ChordLift.proof`. -/
theorem proof_of_rose (hrose : P10ChordLift.RoseStepStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  proof_of_cases P10ChordLift.proof hrose

/-- **A reduction of the rose case to a gap `Gap`** (the shape of the endpoints
`P10Rose.rose_of_regionMoveSubArc` and `P10Rose.rose_of_inPlaceStep` of lane gl-p10-02, whose module
`P10Rose/Live/Reduction` is not on disk yet): `Gap` implies `P10ChordLift.RoseStepStatement`. -/
def RoseReductionStatement (Gap : Prop) : Prop :=
  Gap → P10ChordLift.RoseStepStatement.{u, w, v}

/-- **The outer-pinch step from a reduction of the rose case and its gap.** -/
theorem proof_of_roseReduction {Gap : Prop} (hred : RoseReductionStatement.{u, w, v} Gap)
    (h : Gap) : PocketOuterPinchStepSectionStatement.{u, w, v} :=
  proof_of_rose (hred h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10.proof_of_cases
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10.proof_of_rose
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10.RoseReductionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10.proof_of_roseReduction
