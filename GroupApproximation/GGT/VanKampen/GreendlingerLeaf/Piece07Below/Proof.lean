import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopyBelow
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.InnerTwoArcLong
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 07 (below form): proper arcs of the cell pocket walk, via route 3

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  `CellPocketWalkProperArcsBelowSectionStatement`
(`Estimating/OsinPocketMultipleEdgeCopyBelow`) is the `hproper` residual of
`relativeGreendlingerQuasiGeodesicLeastArea_of_eightResiduals` (`GreendlingerLeaf/Common/EightResidualWaist`).

## Why this module replaces `GreendlingerLeaf/Piece07/Proof`

`Piece07/Proof.lean` sets `proof := CellPocketWalkProperArcsSectionStatement.toBelow
P07LakeExclusion.proof`.  No declaration `P07LakeExclusion.proof` exists, so that module does not build.
The sub-leaf proves the below form directly, so there is no `.toBelow` here (QUEUE).  The assembly
(`GreendlingerLeaf/Assembly`) should import this module and use `Piece07Below.proof_of_innerPocketEnclosed`
(or, once lane `gl-p07-15` lands, the unconditional `Piece07Below.proof`) in place of `Piece07.proof`.

## The route-3 chain

1. **The enclosed inner pocket.**  The residual is `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`
   (`P07LakeExclusion/InnerTwoArcLong`).  It gives an `EnclosedFaceSetSucc` holding a relator cell, whose
   inverse outside walk reads `s₁ Ā₁ s₂ Ā₂` with `|s₁|, |s₂| ≤ ε`.
2. **The long-word inner two-arc pocket.**  `innerTwoArcLong_of_innerPocketEnclosed` turns this into
   `Piece06.LakeFillTwoArcExit` by the two-arc doubling and unpinch `lakeFillTwoArcExit_of_enclosed`
   (`InnerTwoArcLongDoubling`, `InnerTwoArcLongUnpinch`).  This is `CellPocketInnerTwoArcLongStatement`,
   which assumes `∀ word ∈ W, 1 < word.length`.
3. **The Route 3 kept cell.**  `proof_of_innerTwoArcLong` (`P07LakeExclusion/InnerTwoArc`):
   * `cellPocketWalkEuler` gives both Euler equalities of the pocket walk.
   * `exists_kept_of_cellPocketRegion_of_leastArea` puts a relator cell `C` inside the walk, off `a ∪ b`.
   * `one_lt_length_of_two_le_rho` supplies the long-word hypothesis from `OsinCCondition` at `2 ≤ ρ`.
4. **The contradiction.**  `Piece06.false_of_lakeFillTwoArcExit` refutes the exit under the inductive
   premise `OsinLemma97Below`, so no full arc occurs.

`P07LakeExclusion.proof_of_innerPocketEnclosed` composes steps 2–4.

## Endpoint and remaining input

* `Piece07Below.proof_of_innerPocketEnclosed`: the target from the enclosed inner pocket residual.
* Lane `gl-p07-15` closes the residual as `P07InnerPocket.innerPocketEnclosed` (module
  `GreendlingerLeaf/P07InnerPocket/Assembly`).  That module is not on disk yet, so this file cannot import
  it.  The unconditional close is then the one line
  `theorem proof : CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} :=
    proof_of_innerPocketEnclosed P07InnerPocket.innerPocketEnclosed`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b)).  It
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece07Below

universe u w v

/-- **Piece 07 of the Greendlinger leaf, below form, from the enclosed inner pocket.**  The proper arcs
of the cell pocket walk (the lake exclusion) hold below the inductive bound, given the combinatorial
residual `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`.  The proof is route 3:
`innerTwoArcLong_of_innerPocketEnclosed`, then `proof_of_innerTwoArcLong`.  There is no `.toBelow`. -/
theorem proof_of_innerPocketEnclosed
    (h : P07LakeExclusion.InnerPocketEnclosedTwoArcStatement.{u, w, v}) :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} :=
  P07LakeExclusion.proof_of_innerPocketEnclosed h

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece07Below

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece07Below.proof_of_innerPocketEnclosed
