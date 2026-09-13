import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PlanarPieces
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94AntiparallelMetric
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SeparatingRemoval
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PendantRemoval
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CornerInsertion
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CuttingChains
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94QuasiGeodesicRespell
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CellArcs
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94BoundaryArcs
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonPartition
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CaseTwo
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4 over its open pieces

Osin (math/0411039v3, §9), Lemma 9.4: "Let `S` denote the sum of lengths of all unbound arcs
of type (A1) in `Δ`.  Then `S < n √ρ`."  `osinLemma94Section_of_residuals` feeds the closed
pieces into `osinLemma94Section_of_planarPieces`:
* the metric half `osinLemma94AntiparallelMetric`;
* the realization `osinLemma94PolygonRealizationInput`, from the respelling surgery
  (`cornerInsertionInput`, `pendantPathRemovalInput`, the separating removal derived from it and
  `quasiGeodesicRespellInput`), the arcs (`osinLemma94CellArcsInput_holds` and
  `osinLemma94BoundaryArcsInput`) and the partition `osinLemma94PolygonPartitionInput`;
* Case 2: `osinLemma94CaseTwoInput`.
The remaining hypotheses are the polygon count and Case 1.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **The realization piece from the partition.**  Each component is cut along `t_1, …, t_l`
into a polygon.  The cutting paths come from the respelling surgery and the arcs are closed, so
only the partition of the face walks into sides stays a hypothesis. -/
theorem osinLemma94PolygonRealizationInput_of_partition
    (hpartition : OsinLemma94PolygonPartitionInput.{u, w, v}) :
    OsinLemma94PolygonRealizationInput.{u, w, v} :=
  osinLemma94PolygonRealizationInput_of_pieces
    (osinLemma94CuttingChainsInput_of_pieces
      (GloballyDistinguishedSectionFamily.chainRespellInput_of_pieces
        GloballyDistinguishedSectionFamily.cornerInsertionInput
        (GloballyDistinguishedSectionFamily.separatingPathRemovalInput_of_pendant
          GloballyDistinguishedSectionFamily.pendantPathRemovalInput))
      GloballyDistinguishedSectionFamily.pendantPathRemovalInput quasiGeodesicRespellInput)
    osinLemma94CellArcsInput_holds osinLemma94BoundaryArcsInput hpartition

/-- **The realization piece holds.**  "Each component is cut along `t_1, …, t_l` into a
polygon", with the partition of the face walks from `osinLemma94PolygonPartitionInput`. -/
theorem osinLemma94PolygonRealizationInput : OsinLemma94PolygonRealizationInput.{u, w, v} :=
  osinLemma94PolygonRealizationInput_of_partition osinLemma94PolygonPartitionInput

/-- **Lemma 9.4 over its open pieces.**  "Let `S` denote the sum of lengths of all unbound arcs
of type (A1) in `Δ`.  Then `S < n √ρ`."  The hypotheses are the polygon count and Case 1. -/
theorem osinLemma94Section_of_residuals
    (hcount : OsinLemma94PolygonCountInput.{u, w, v})
    (hone : OsinLemma94CaseOneInput.{u, w, v}) :
    OsinLemma94SectionStatement.{u, w, v} :=
  osinLemma94Section_of_planarPieces osinLemma94AntiparallelMetric
    osinLemma94PolygonRealizationInput hcount hone osinLemma94CaseTwoInput

#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94PolygonRealizationInput_of_partition
#audit_closed_axioms GroupApproximation.GGT.VanKampen.osinLemma94PolygonRealizationInput
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94Section_of_residuals

end GroupApproximation.GGT.VanKampen
