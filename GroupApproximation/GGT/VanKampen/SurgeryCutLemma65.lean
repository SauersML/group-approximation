import GroupApproximation.GGT.VanKampen.Estimating.Lemma65Statement
import GroupApproximation.GGT.VanKampen.SurgeryCutDiagram

/-!
# The cut as Osin's Lemma 6.5 data

`SurgeryCutDiagram` builds the subdiagram a closed walk encloses, with its cell
count drop and its inherited reducedness.  This file hands those to the landed
record of Osin's Lemma 6.5.  Its remaining field is the positivity of the
piece's cell count, which comes from the definition of the distinguished family
rather than from the surgery.
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

/-- **Osin's Lemma 6.5 cut, as data.**  Everything except the positivity of the
piece's cell count, which comes from the definition of the distinguished family
rather than from the surgery. -/
noncomputable def toLemma65CutData (cut : RegionCutData Delta)
    (hred : Delta.Reduced) (hpos : 0 < cut.diagram.rCellCount) :
    Embedded.Lemma65CutData Delta where
  enclosed := cut.diagram
  rCellCount_lt := cut.diagram_rCellCount_lt
  rCellCount_pos := hpos
  reduced := cut.diagram_reduced hred

end RegionCutData
end MapCollapse
end Surgery
end VanKampen
end GGT
end GroupApproximation
