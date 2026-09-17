import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist.Endpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The least-area Greendlinger leaf at `.{0,0,0}` for the alternative printed forms

Lane gl-assembly-09: the alternative printed forms of `sec:torsion-free` of
`non_mf_groups_exist.tex` (module `TorsionFreeGreendlingerForms`, 17 theorems at lines 51–215),
with the hypothesis `hgreendlinger` removed.

## Planned route and why it is not available yet

The lane was planned to apply each `TorsionFreeGreendlingerForms.*_of_greendlinger` theorem to the
hypothesis-free leaf `GreendlingerLeaf.AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed`
(lane gl-assembly-04).  That theorem is not on disk: the region endpoints for residuals 01, 04, 06,
07 and 10 of the Below waist are still in flight.

The interface this lane consumes from the upstream lanes is already on disk as a Statement:
`GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement` (lane
gl-assembly-02), the conjunction of the five open residuals, with its reduction
`AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_openResidualsBelow`, in which the closed
trio (residuals 05, 08, 09) is discharged by `AsmWaist.closedTrio`.  Following the author brief, this
lane imports that Statement rather than restating it.  This matches lanes gl-assembly-05 and
gl-assembly-08.

## Why this is progress and not a restatement

The existing forms take the whole leaf `RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0,0,0}`
(Osin, math/0411039, Lemma 4.4 at least-area diagrams) as a hypothesis.  The forms of this lane take
only the five open residuals: the proof content of the eight-binder Below waist and of the three
closed residuals is supplied.  So the remaining hypothesis is strictly smaller in proof content.
It is true: each residual is a section form of Osin's Lemmas 9.4 and 9.7(b) (see
`lanes/carto-gl-assembly.md`, section 2).

Once lane gl-assembly-04 lands, each form closes as
`TorsionFreeGreendlingerForms.<name>_of_greendlinger AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed.{0,0,0}`,
or by feeding the five region endpoints to `manuscriptSentence_<name>Form_of_openResidualsBelow`.

## Manuscript status

Infrastructure; certifies no printed sentence on its own.
-/

namespace GroupApproximation.Manuscript.NonMF.GreendlingerClosedForms

/-- **Osin's Lemma 4.4 at least-area diagrams, at universes `.{0,0,0}`, from the five open
residuals of the Below waist.**  The closed trio is supplied by `AsmWaist.closedTrio`. -/
theorem leastAreaLeaf_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0} :=
  GGT.VanKampen.GreendlingerLeaf.AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_openResidualsBelow.{0, 0, 0}
    hopen

end GroupApproximation.Manuscript.NonMF.GreendlingerClosedForms

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedForms.leastAreaLeaf_of_openResidualsBelow
