import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEndpoint.SingleRegion
import GroupApproximation.Meta.AxiomGuard

/-!
# The rose endpoint chain, part 2: the endpoint module downstream of every reduction

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane gl-p10-04 (b).  This module sits downstream of the whole live rose
chain (`P10Rose/Live/Reduction/InPlace`, `P10Rose/Live/Reduction`, `P10RoseEndpoint/SingleRegion`)
and of the case assembly `Piece10Live/Cases`, so the endpoint `P10Rose.rose` and the unconditional
`Piece10.proof` can live here without the import cycle of `P10Rose/Proof` (every reduction module
imports that one) and of `Piece10/Proof` (which cites the missing `P10Rose.rose`).

## Status: the endpoint is NOT closed

`P10Rose.rose : P10ChordLift.RoseStepStatement` needs an unconditional closer of
`P10Rose.RoseSingleRegionMoveStatement` (module `P10RoseEndpoint/SingleRegion`) or of the weaker
`P10Rose.RoseRegionMoveSubArcStatement` (module `P10Rose/Live/Reduction`).  None exists on disk.
The planned closer is lane gl-p10-08 (`GreendlingerLeaf/P10RoseExtremal`, not on disk at authoring time):
a reduction `singleRegionMove_of_extremalRegion : RoseExtremalRegionStatement →
RoseSingleRegionMoveStatement` which re-lists the kept darts as a closed walk (balance from
`P10RoseKeptBalance`, Euler re-listing from `P10RoseEuler`), leaving the planarity content (an
extremal region meets the arcs only in a prefix, a suffix or a whole arc) as its gap.

So this module states the shape of such a closer as a Statement over its gap,
`RoseSingleRegionCloserStatement Gap := Gap → RoseSingleRegionMoveStatement`, and proves the
`_of_` endpoints

* `P10Rose.rose_of_singleRegionCloser`: the rose case from a closer and its gap;
* `Piece10.proof_of_singleRegionCloser`: the outer-pinch step from a closer and its gap.

The remaining gap after this lane is `P10Rose.RoseSingleRegionMoveStatement` itself (or the gap of
lane gl-p10-08).  Everything between it and `PocketOuterPinchStepSectionStatement` is proved:
`regionMoveSubArc_of_singleRegionMove`, `inPlaceStep_of_regionMoveSubArc`,
`combinatorialStep_of_inPlaceStep`, `rose_of_combinatorialStep`, `Piece10.proof_of_cases`, with the
non-rose case closed by `P10ChordLift.proof`.

## The unconditional endpoints, once a closer exists

With `hred := singleRegionMove_of_extremalRegion` and `hgap : RoseExtremalRegionStatement` (or, for
a direct closer `hclose : RoseSingleRegionMoveStatement`, `Gap := True`, `hred := fun _ => hclose`),
in this module:

```
theorem P10Rose.rose : P10ChordLift.RoseStepStatement.{u, w, v} :=
  P10Rose.rose_of_singleRegionCloser hred hgap
theorem Piece10.proof : PocketOuterPinchStepSectionStatement.{u, w, v} :=
  Piece10.proof_of_rose P10Rose.rose
```

## Truth check

`P10ChordLift.RoseStepStatement` is expected TRUE (Osin 9.7(b), the rose case of the outer pinch
step).  `RoseSingleRegionMoveStatement` is PLAUSIBLE only: supported by search (every rose
configuration with at most five walk darts, about a hundred random ones with six to twelve), not by
a proof.  `RoseRegionMoveSubArcStatement` is logically weaker than it and passes the same tests.
The generic closer shape `RoseSingleRegionCloserStatement Gap` is a plain implication; the lemmas
here are composition only.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

universe u w v

/-- **A closer of the single-region move over a gap `Gap`** (the shape of the endpoint
`singleRegionMove_of_extremalRegion` of lane gl-p10-08, not on disk at authoring time): `Gap`
implies `RoseSingleRegionMoveStatement`. -/
def RoseSingleRegionCloserStatement (Gap : Prop) : Prop :=
  Gap → RoseSingleRegionMoveStatement.{u, w, v}

/-- **The rose case from a closer of the single-region move and its gap.** -/
theorem rose_of_singleRegionCloser {Gap : Prop}
    (hred : RoseSingleRegionCloserStatement.{u, w, v} Gap) (h : Gap) :
    P10ChordLift.RoseStepStatement.{u, w, v} :=
  rose_of_singleRegionMove (hred h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10

universe u w v

/-- **The outer-pinch step from a closer of the single-region move and its gap.** -/
theorem proof_of_singleRegionCloser {Gap : Prop}
    (hred : P10Rose.RoseSingleRegionCloserStatement.{u, w, v} Gap) (h : Gap) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  proof_of_rose (P10Rose.rose_of_singleRegionCloser hred h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.RoseSingleRegionCloserStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.rose_of_singleRegionCloser
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10.proof_of_singleRegionCloser
