import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopyBelow
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.Proof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 07: proper arcs of the cell pocket walk, below the inductive bound

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  `CellPocketWalkProperArcsBelowSectionStatement`
(`Estimating/OsinPocketMultipleEdgeCopyBelow`) is the `hproper` residual of
`relativeGreendlingerQuasiGeodesicLeastArea_of_eightResiduals` (`GreendlingerLeaf/Common/EightResidualWaist`).

## Route

`CellPocketWalkProperArcsSectionStatement.toBelow` (`Estimating/OsinPocketMultipleEdgeCopyBelow`), at the
same thresholds, applied to the lake exclusion: a full arc of the cell pocket walk would make its cell a
lake of the complement of the walk (model test in `Estimating/OsinPocketMultipleEdgeCopyOrderSection`).

## Assumed sub-leaf endpoint

The sub-leaf lives in the module `GreendlingerLeaf/P07LakeExclusion/Proof` and exposes

* `GreendlingerLeaf.P07LakeExclusion.proof : CellPocketWalkProperArcsSectionStatement.{u, w, v}`.

If instead it proves the below form `CellPocketWalkProperArcsBelowSectionStatement.{u, w, v}` directly
(which may use the inductive premise `OsinLemma97Below`), the body of `proof` is that theorem itself,
without `toBelow`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece07

universe u w v

/-- **Piece 07 of the Greendlinger leaf: `CellPocketWalkProperArcsBelowSectionStatement` holds**, with no
hypotheses: the proper arcs of the cell pocket walk (the lake exclusion), in their below form. -/
theorem proof : CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} :=
  CellPocketWalkProperArcsSectionStatement.toBelow GreendlingerLeaf.P07LakeExclusion.proof

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece07

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece07.proof
