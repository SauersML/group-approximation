import GroupApproximation.GGT.VanKampen.Estimating.SelectionDichotomy
import GroupApproximation.GGT.VanKampen.Estimating.OrderedReplacement
import GroupApproximation.Meta.AxiomGuard

/-!
# Lemma 65(a) reduced to one dichotomy, with the corrected replacement

`Estimating/SelectionDichotomy.lean` reduces
`EstimatingSelectionConstructionStatement` to one geometric dichotomy per
reduced diagram, and states the drop branch with `Surgery.GRegionReplacement`.
That datatype carries a `Surgery.RCellEquiv`, a bijection between the two maps'
**full potential-relator-record types**, and
`SurgeryRCellEquivCounterexample.no_historical_transport` refutes that
requirement outright: two explicit discs with the same boundary and empty
relator lists, where the new polygon has a `G`-face admitting an unlisted
relator record and the old one-edge map has none.  A collapse that drops faces
is precisely where the two record types differ, so the historical drop branch
asks a producer for a datatype the counterexample rules out.

`Surgery.OrderedRCellTransport` is the corrected interface of issue #205: only
the ordered relator **word** and **value** lists are required to agree, which is
what a `G`-region collapse preserves, and which is all that
`Surgery.OrderedGRegionReplacement.oEquivalent` and `.reduced` consume.

This file states the same dichotomy with that interface and closes the
construction from it, through
`selectionFaceDropOracle_of_orderedGRegionReplacements`.  The terminal branch is
unchanged, so the only difference between the two statements is which
replacement the drop branch has to produce.

`lemma65aOrderedDichotomy_of_lemma65aDichotomy` proves the ordered form is the
**weaker** of the two, by `Surgery.OrderedGRegionReplacement.ofHistorical`.  So
this is a relaxation of an obligation, not a substitute problem: any proof of
the historical dichotomy still gives the construction, through this file.

`Surgery.MapCollapse.InteriorGCellRegion.collapseReplacement`
(`GGT/VanKampen/SurgeryGCellCollapse.lean`) inhabits the drop branch from a disc
region of interior `G`-cells, with `collapseReplacement_faceCount_lt` for the
face drop.  What is left of Lemma 65(a) is therefore Osin's geometry — producing
the region and the value-one boundary cycle, his elimination of condition `(∗)`
— and no longer a datatype that cannot be built.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u w v

/-- **The Lemma 65(a) dichotomy, with the corrected replacement interface.**

For every reduced, positive-cell, quasi-geodesic diagram: either some scaffold
carries the hereditary planar edge bound and the admissible exterior merge, or
the diagram admits an **ordered** region replacement with a strictly smaller
ambient face count.

Identical to `Lemma65aDichotomyStatement` except in the drop branch, where
`Surgery.OrderedGRegionReplacement` replaces `Surgery.GRegionReplacement`. -/
def Lemma65aOrderedDichotomyStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    (∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
      ∀ lambda c mu : ℝ,
        0 < lambda → lambda ≤ 1 → 0 ≤ c →
        0 < mu → mu ≤ 1 / 16 →
          ∃ (eps rho : ℕ) (kappa c1 c2 : ℝ),
            UnboundEstimate.OsinUnboundScale lambda c mu kappa c1 c2 eps rho ∧
            ∀ (W : Set (List (GGT.RelLetter G Lambda))),
              OsinCCondition D W eps mu lambda c rho →
                ∀ Delta : DiscDiagram.{u, w, v} W,
                  Delta.Reduced → 0 < Delta.rCellCount →
                  IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord →
                  (∃ scaffold : EstimatingScaffold D eps Delta,
                    HasHereditaryPlanarEdgeBound
                        (Embedded.InteriorEdge.Incident
                          (selected := scaffold.selected.family)) ∧
                      Embedded.ExteriorMergeAvailable
                        scaffold.selected.family) ∨
                  ∃ replacement :
                      Surgery.OrderedGRegionReplacement.{u, w, v, v} Delta,
                    replacement.diagram.toCombMap.faceCount <
                      Delta.toCombMap.faceCount

/-- **The selection construction from the corrected dichotomy.**  The face-count
induction, the `O`-equivalence composition and the replacement retyping are all
landed, and loop separation is free, so the dichotomy is the whole remaining
input — now asked for with the replacement interface that a face-dropping
collapse can actually supply. -/
theorem estimatingSelectionConstruction_of_lemma65aOrderedDichotomy
    (hdichotomy : Lemma65aOrderedDichotomyStatement.{u, w, v}) :
    EstimatingSelectionConstructionStatement.{u, w, v} := by
  apply estimatingSelectionConstruction_of_faceDropOracles
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨eps, rho, kappa, c1, c2, hscale, hdich⟩ :=
    hdichotomy D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨eps, rho, kappa, c1, c2, hscale, ?_⟩
  intro W hcondition
  apply selectionFaceDropOracle_of_orderedGRegionReplacements
  intro Delta hred hcells hboundary
  rcases hdich W hcondition Delta hred hcells hboundary with
    ⟨scaffold, hplanar, hmerge⟩ | hdrop
  · exact Or.inl ⟨scaffold,
      estimatingGraphData_of_planar_and_merge scaffold hplanar hmerge⟩
  · exact Or.inr hdrop

/-- **The ordered dichotomy is the weaker obligation.**  A historical
replacement maps into the corrected one by
`Surgery.OrderedGRegionReplacement.ofHistorical`, keeping its diagram and so its
face count, so nothing proved against `Lemma65aDichotomyStatement` is lost by
working with the ordered form. -/
theorem lemma65aOrderedDichotomy_of_lemma65aDichotomy
    (h : Lemma65aDichotomyStatement.{u, w, v}) :
    Lemma65aOrderedDichotomyStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨eps, rho, kappa, c1, c2, hscale, hdich⟩ :=
    h D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨eps, rho, kappa, c1, c2, hscale, ?_⟩
  intro W hcondition Delta hred hcells hboundary
  rcases hdich W hcondition Delta hred hcells hboundary with
    hterminal | ⟨replacement, hface⟩
  · exact Or.inl hterminal
  · exact Or.inr
      ⟨Surgery.OrderedGRegionReplacement.ofHistorical replacement, hface⟩

end VanKampen
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.VanKampen.estimatingSelectionConstruction_of_lemma65aOrderedDichotomy

#audit_axioms GroupApproximation.GGT.VanKampen.lemma65aOrderedDichotomy_of_lemma65aDichotomy
