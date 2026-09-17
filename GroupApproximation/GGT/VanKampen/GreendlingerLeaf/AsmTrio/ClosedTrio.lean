import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece05.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.Proof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf assembly: the closed trio of residuals 05, 08 and 09

Osin, arXiv:math/0411039v3, Lemma 4.4 at least-area diagrams (the Greendlinger waist of Hull's
Theorem 7.1, used for `thm:hull`, tex 1636/2122 of `non_mf_groups_exist.tex`).

The Below waist `relativeGreendlingerQuasiGeodesicLeastArea_of_eightResidualsBelow`
(`GreendlingerLeaf/Common/EightResidualWaistBelow`) has eight binders.  Three of them are already
produced by hypothesis-free theorems:

* binder `htwocopy`, `OsinTwoGonCleanCopySectionStatement` (Osin's Appendix, clean copies of
  two-gons): `GreendlingerLeaf.Piece05.proof`, the six clean-copy steps
  `P05Spur/OuterCell/OuterSide/CellSide/CellHair/RegionPair.proof` assembled by
  `osinTwoGonCleanCopySection_of_steps`;
* binder `hfaces`, `OsinSectionPocketFaceSetProperSectionStatement` (a proper source arc for the
  section pocket): `GreendlingerLeaf.P08ProperArc.proof`, with thresholds `ε₀ = 0`, `ρ₀ = 1`;
* binder `hwhole`, `OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement` (the two-arc face
  set on a whole section, Osin's Lemma 9.7(b)): `GreendlingerLeaf.Piece09.proof`, with thresholds
  `ε₀ = 0`, `ρ₀ = 1`.

This module bundles them as one closed conjunction, `AsmTrio.closedTrio`, with the three aliases
`AsmTrio.twoCopy`, `AsmTrio.faces` and `AsmTrio.whole`, for the open-residual waist interface
(lane gl-assembly-02) and the unconditional leaf (gl-assembly-04).

## Import hygiene

Only `Piece05/Proof`, `P08ProperArc/Proof` and `Piece09/Proof` are imported.  Their transitive
closure (1791 modules) contains none of the broken modules `GreendlingerLeaf/Assembly`,
`Piece01/Proof`, `Piece04/Proof`, `Piece04/Residual`, `Piece06/Proof`, `Piece07/Proof`,
`Piece10/Proof`.  The P05 sub-leaves repeat short names (`hasCleanTwoGon_of_transport`,
`RegionTransport`, `transport`) but each in its own namespace `GreendlingerLeaf.P05<Dir>`, and this
module opens none of them.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 4.4 and the
Appendix); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmTrio

universe u w v

/-- **The closed trio of Greendlinger leaf residuals**: residuals 05 (`htwocopy`), 08 (`hfaces`)
and 09 (`hwhole`) of `relativeGreendlingerQuasiGeodesicLeastArea_of_eightResidualsBelow` hold,
with no hypotheses. -/
theorem closedTrio :
    OsinTwoGonCleanCopySectionStatement.{u, w, v} ∧
      OsinSectionPocketFaceSetProperSectionStatement.{u, w, v} ∧
        OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement.{u, w, v} :=
  ⟨GreendlingerLeaf.Piece05.proof, GreendlingerLeaf.P08ProperArc.proof,
    GreendlingerLeaf.Piece09.proof⟩

/-- **Residual 05 (`htwocopy`)**: clean copies of two-gons, uniformly in the parameters. -/
theorem twoCopy : OsinTwoGonCleanCopySectionStatement.{u, w, v} :=
  GreendlingerLeaf.Piece05.proof

/-- **Residual 08 (`hfaces`)**: the proper face set producer, uniformly in the parameters. -/
theorem faces : OsinSectionPocketFaceSetProperSectionStatement.{u, w, v} :=
  GreendlingerLeaf.P08ProperArc.proof

/-- **Residual 09 (`hwhole`)**: the two-arc producer at a whole section, uniformly in the
parameters. -/
theorem whole : OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement.{u, w, v} :=
  GreendlingerLeaf.Piece09.proof

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmTrio

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmTrio.closedTrio
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmTrio.closedTrio
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmTrio.twoCopy
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmTrio.twoCopy
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmTrio.faces
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmTrio.faces
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmTrio.whole
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmTrio.whole
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece05.proof
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc.proof
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.proof
