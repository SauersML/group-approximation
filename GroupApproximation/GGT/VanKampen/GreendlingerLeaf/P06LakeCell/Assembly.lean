import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.AssemblyStatements
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Assembly.CellStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06, case (d): assembly of the lakes surgery from its three cases

* `lakesSurgery_of_cases`: `Piece06.CellRoseLakesSurgeryBelowStatement` from
  `CellRoseLakesOutsideCellStatement`, `CaseDLakeRelatorExitStatement` and
  `CellRoseLakeGOnlyBelowStatement`.  The thresholds are `ε₀ = max (max ε₁ ε₂) ε₃` and
  `ρ₀ = max (max ρ₁ ρ₂) ρ₃`.  At fixed parameters, `cases_core` splits on `AllCellsEnclosed K`:
  * a relator cell in the exterior piece goes to the first statement;
  * all cells enclosed, with a second relator cell in the lake of `Π_i` or of `Π_j`, goes to the
    exit statement, whose two exits are the first two disjuncts;
  * all cells enclosed, with both lakes `G`-only, goes to the `G`-only statement.
* `cellStep_of_cases`: residual 06 (`CellPocketOuterPinchStepSectionDistinctBelowStatement`),
  through the landed `P06Assembly.cellStep_of_surgery` (gl-p06-04 (iii): LakesSurgery:156,
  LakesBelow:98, RoseBelow:136 and `Piece06.MonogonCorner.badCornerRefinement`).
* `outsideCell_of_surgery`, `gOnly_of_surgery`: the target implies the first and third case
  statements at the same thresholds, so neither is stronger than the target.

The exterior case `CellRoseLakesOutsideCellStatement` is not proved here.  Its route: with a
relator cell of `E₀` off the filled `F'` and both `Π_i, Π_j ∈ F'`, the outside walk reads `s₁' s₂'`,
which is refuted by the short-petal exit (`Piece06.shortPetalFree_of_below`, RoseBelow:74);
otherwise cases (a) and (c) of LakesSurgery give the two lake-fill exits.

The `hcellStep`-typed endpoint stays circular in case (d) (carto-gl-p06 §2).  Binder 5 bypasses it
(gl-p06-01..03).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.Assembly

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated

/-- **The lakes surgery from its three cases.**  Take the maxima of the three thresholds and split
on `cases_core`. -/
theorem lakesSurgery_of_cases (hout : CellRoseLakesOutsideCellStatement.{u, w, v})
    (hexit : CaseDLakeRelatorExitStatement.{u, w, v})
    (hgonly : CellRoseLakeGOnlyBelowStatement.{u, w, v}) :
    Piece06.CellRoseLakesSurgeryBelowStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨e1, he1⟩ := hout D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨e2, he2⟩ := hexit D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨e3, he3⟩ := hgonly D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max (max e1 e2) e3, fun eps heps => ?_⟩
  have hleft : max e1 e2 ≤ eps := (le_max_left (max e1 e2) e3).trans heps
  obtain ⟨r1, hr1, hrho1⟩ := he1 eps ((le_max_left e1 e2).trans hleft)
  obtain ⟨r2, _, hrho2⟩ := he2 eps ((le_max_right e1 e2).trans hleft)
  obtain ⟨r3, _, hrho3⟩ := he3 eps ((le_max_right (max e1 e2) e3).trans heps)
  refine ⟨max (max r1 r2) r3,
    lt_of_lt_of_le hr1 ((le_max_left r1 r2).trans (le_max_left (max r1 r2) r3)),
    fun rho hrho W hcondition X i j hij hlea hbelow hlabel K hK hnft hfirst hsecond hpinch hrose
      hcut hside hshort hmove => ?_⟩
  have hrleft : max r1 r2 ≤ rho := (le_max_left (max r1 r2) r3).trans hrho
  have h1 : r1 ≤ rho := (le_max_left r1 r2).trans hrleft
  have h2 : r2 ≤ rho := (le_max_right r1 r2).trans hrleft
  have h3 : r3 ≤ rho := (le_max_right (max r1 r2) r3).trans hrho
  exact cases_core K
    (fun hall => hrho1 rho h1 W hcondition X i j hij hlea hbelow hlabel K hK hnft hfirst hsecond
      hpinch hrose hcut hside hshort hmove hall)
    (fun hall hsec => (hrho2 rho h2 W hcondition X i j hij hlea hbelow hlabel K hK hnft hfirst
      hsecond hpinch hrose hcut hside hshort hmove hall hsec).elim Or.inl
        (fun htwo => Or.inr (Or.inl htwo)))
    (fun hall hgi hgj => hrho3 rho h3 W hcondition X i j hij hlea hbelow hlabel K hK hnft hfirst
      hsecond hpinch hrose hcut hside hshort hmove hall hgi hgj)

/-- **Residual 06 from the three cases**, through the landed Piece06 chain and the monogon
corner. -/
theorem cellStep_of_cases (hout : CellRoseLakesOutsideCellStatement.{u, w, v})
    (hexit : CaseDLakeRelatorExitStatement.{u, w, v})
    (hgonly : CellRoseLakeGOnlyBelowStatement.{u, w, v}) :
    CellPocketOuterPinchStepSectionDistinctBelowStatement.{u, w, v} :=
  P06Assembly.cellStep_of_surgery (lakesSurgery_of_cases hout hexit hgonly)

/-- **The exterior case from the target**, at the same thresholds, ignoring the extra
hypothesis. -/
theorem outsideCell_of_surgery (h : Piece06.CellRoseLakesSurgeryBelowStatement.{u, w, v}) :
    CellRoseLakesOutsideCellStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hcond X i j hij hlea hbelow hlabel K hK hnft hfirst hsecond
    hpinch hrose hcut hside hshort hmove _ => hrho rho hrho' W hcond X i j hij hlea hbelow hlabel K
      hK hnft hfirst hsecond hpinch hrose hcut hside hshort hmove⟩

/-- **The `G`-only case from the target**, at the same thresholds, ignoring the extra
hypotheses. -/
theorem gOnly_of_surgery (h : Piece06.CellRoseLakesSurgeryBelowStatement.{u, w, v}) :
    CellRoseLakeGOnlyBelowStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hcond X i j hij hlea hbelow hlabel K hK hnft hfirst hsecond
    hpinch hrose hcut hside hshort hmove _ _ _ => hrho rho hrho' W hcond X i j hij hlea hbelow
      hlabel K hK hnft hfirst hsecond hpinch hrose hcut hside hshort hmove⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.Assembly

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.Assembly.lakesSurgery_of_cases
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.Assembly.cellStep_of_cases
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.Assembly.outsideCell_of_surgery
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.Assembly.gOnly_of_surgery
