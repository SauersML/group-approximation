import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PlanarPieces
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94AntiparallelMetric
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SeparatingRemoval
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PendantRemoval
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CuttingChains
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94QuasiGeodesicRespell
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CellArcs
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4 over its open pieces

Osin (math/0411039v3, §9), Lemma 9.4: "Let `S` denote the sum of lengths of all unbound arcs
of type (A1) in `Δ`.  Then `S < n √ρ`."  `osinLemma94Section_of_residuals` feeds the closed
pieces into `osinLemma94Section_of_planarPieces`:
* the metric half `osinLemma94AntiparallelMetric`;
* the pendant removal `pendantPathRemovalInput`, and the separating removal derived from it;
* the respelling `quasiGeodesicRespellInput` and the relator arcs
  `osinLemma94CellArcsInput_holds`.
The remaining hypotheses are the pieces still open.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **The realization piece over its open parts.**  Each component is cut along `t_1, …, t_l`
into a polygon.  The cutting paths come from the respelling surgery, the relator arcs are closed,
and the boundary arcs and the partition stay hypotheses. -/
theorem osinLemma94PolygonRealizationInput_of_residuals
    (hinsert : GloballyDistinguishedSectionFamily.CornerInsertionInput.{u, w, v})
    (hboundary : OsinLemma94BoundaryArcsInput.{u, w, v})
    (hpartition : OsinLemma94PolygonPartitionInput.{u, w, v}) :
    OsinLemma94PolygonRealizationInput.{u, w, v} :=
  osinLemma94PolygonRealizationInput_of_pieces
    (osinLemma94CuttingChainsInput_of_pieces
      (GloballyDistinguishedSectionFamily.chainRespellInput_of_pieces hinsert
        (GloballyDistinguishedSectionFamily.separatingPathRemovalInput_of_pendant
          GloballyDistinguishedSectionFamily.pendantPathRemovalInput))
      GloballyDistinguishedSectionFamily.pendantPathRemovalInput quasiGeodesicRespellInput)
    osinLemma94CellArcsInput_holds hboundary hpartition

/-- **Lemma 9.4 over its open pieces.**  "Let `S` denote the sum of lengths of all unbound arcs
of type (A1) in `Δ`.  Then `S < n √ρ`."  The hypotheses are the corner insertion, the boundary
arcs, the partition, the polygon count and the two cases. -/
theorem osinLemma94Section_of_residuals
    (hinsert : GloballyDistinguishedSectionFamily.CornerInsertionInput.{u, w, v})
    (hboundary : OsinLemma94BoundaryArcsInput.{u, w, v})
    (hpartition : OsinLemma94PolygonPartitionInput.{u, w, v})
    (hcount : OsinLemma94PolygonCountInput.{u, w, v})
    (hone : OsinLemma94CaseOneInput.{u, w, v})
    (htwo : OsinLemma94CaseTwoInput.{u, w, v}) :
    OsinLemma94SectionStatement.{u, w, v} :=
  osinLemma94Section_of_planarPieces osinLemma94AntiparallelMetric
    (osinLemma94PolygonRealizationInput_of_residuals hinsert hboundary hpartition)
    hcount hone htwo

#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94PolygonRealizationInput_of_residuals
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94Section_of_residuals

end GroupApproximation.GGT.VanKampen
