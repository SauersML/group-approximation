import GroupApproximation.GGT.VanKampen.Estimating.Lemma65Statement
import GroupApproximation.GGT.VanKampen.SurgeryCutDiagram
import GroupApproximation.Meta.AxiomGuard

/-!
# The cut as Osin's Lemma 6.5 data

`SurgeryCutDiagram` builds the subdiagram a closed walk encloses, with its cell
count drop and its inherited reducedness.  This file hands those to the landed
record of Osin's Lemma 6.5. The geometric producer also supplies positivity of
the piece's cell count and its boundary decomposition into at most four
quasi-geodesic sections. These are separate from the cut's planar map.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Surgery
namespace MapCollapse

universe u w v

namespace RegionCutData

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}

/-- The actual cut, together with its positive cell count and quasi-geodesic
boundary sections, supplies every field of the current Lemma 6.5 cut record. -/
noncomputable def toLemma65CutData (cut : RegionCutData Delta)
    (D : RelGenSet G Lambda) (lambda c : ℝ)
    (hred : Delta.Reduced) (hpos : 0 < cut.diagram.rCellCount)
    (sections : Embedded.BoundarySections D lambda c cut.diagram) :
    Embedded.Lemma65CutData D lambda c Delta where
  enclosed := cut.diagram
  rCellCount_lt := cut.diagram_rCellCount_lt
  rCellCount_pos := hpos
  reduced := cut.diagram_reduced hred
  sections := sections

end RegionCutData
end MapCollapse
end Surgery
end VanKampen
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutData.toLemma65CutData
