import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist.Endpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The least-area Greendlinger leaf at `.{0,0,0}` over the five open residuals

Lane gl-assembly-08 (proof-step sentences of `sec:torsion-free`, tex lines 2129–2182 of
`non_mf_groups_exist.tex`) was planned to apply the hypothesis-free leaf
`GreendlingerLeaf.AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed` (lane gl-assembly-04).
That theorem is not on disk: the five region endpoints (residuals 01, 04, 06, 07 and 10 of the
Below waist) are still in flight.

The interface this lane consumes from the upstream lanes is already on disk as a Statement:
`GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement` (lane gl-assembly-02), the
conjunction of the five open residuals, with its reduction
`AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_openResidualsBelow`, in which the closed
trio (residuals 05, 08, 09) is already discharged.  Following the author brief, this lane imports
that Statement rather than restating it.

## Why this is progress and not a restatement

The existing carriers (`TorsionFreeGreendlingerLeaf`, `TorsionFreeGreendlingerSentences`) take the
whole leaf `RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0,0,0}` as a hypothesis.  The
carriers of this lane take only the five open residuals: the proof content of the three closed
residuals and of the eight-binder Below waist is supplied.  So the remaining hypothesis is strictly
smaller in proof content.  It is true: each residual is a section form of Osin's Lemmas 9.4 and
9.7(b) (see `lanes/carto-gl-assembly.md`, section 2).

Once lane gl-assembly-04 lands, it produces the five residuals, and each carrier closes by
applying them.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace GreendlingerClosedSteps

/-- **Osin's Lemma 4.4 at least-area diagrams, at universes `.{0,0,0}`, from the five open
residuals of the Below waist.** -/
theorem leastAreaLeaf_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0} :=
  GGT.VanKampen.GreendlingerLeaf.AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_openResidualsBelow.{0, 0, 0}
    hopen

end GreendlingerClosedSteps
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedSteps.leastAreaLeaf_of_openResidualsBelow
