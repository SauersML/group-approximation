import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.Cases
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.Live.Reduction.InPlace
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 10 (live): the step from the in-place rose step

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-03: the outer-pinch step
`PocketOuterPinchStepSectionStatement` from the in-place rose gap `P10Rose.RoseInPlaceStepStatement`
of the live reduction chain (`GreendlingerLeaf/P10Rose/Live/Reduction/InPlace`, lane gl-p10-02), through
`P10Rose.rose_of_inPlaceStep` and `Piece10.proof_of_rose` (`GreendlingerLeaf/Piece10Live/Cases`).
The non-rose case is closed unconditionally by `P10ChordLift.proof`.

* `proof_of_inPlaceStep`: the step from `RoseInPlaceStepStatement`.

The companion `proof_of_regionMoveSubArc` waits for the sub-arc module of lane gl-p10-02; its text is
in the docstring of `Piece10Live/Cases`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10

universe u w v

/-- **The outer-pinch step from the in-place rose step.** -/
theorem proof_of_inPlaceStep (h : P10Rose.RoseInPlaceStepStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  proof_of_rose (P10Rose.rose_of_inPlaceStep h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10.proof_of_inPlaceStep
