import GroupApproximation.Higman.PairedReturnAmbientResiduallyFinite

/-!
# The profinite obstruction for the five-generator cutter

The five-generator cutter meets the canonical left factor in Higman's
infinite conjugator graph.  Profinite closure is functorial under preimages,
so closedness of the cutter necessarily implies closedness of that graph in
`F₃ × F₃`.  This isolates the exact extra separability theorem needed
beyond residual finiteness of the paired ambient itself.
-/

namespace GroupApproximation
namespace Higman
namespace PairedReturnFiveCutterProfiniteReduction

open PairedReturnCutter

/-- The profinite closure of the conjugator graph maps into the pullback of
the profinite closure of the five-generator cutter. -/
theorem profiniteClosure_graphSub_le_comap_fiveCutterClosure :
    profiniteClosure Star.graphSub ≤
      (profiniteClosure fiveCutter).comap
        (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC) := by
  rw [← fiveCutter_comap_left]
  exact profiniteClosure_comap_le fiveCutter
    (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC)

/-- Any proof that the five-generator cutter is profinitely closed must, in
particular, prove Higman's infinite conjugator graph profinitely closed. -/
theorem profiniteClosure_graphSub_of_fiveCutter_closed
    (hfive : profiniteClosure fiveCutter = fiveCutter) :
    profiniteClosure Star.graphSub = Star.graphSub := by
  rw [← fiveCutter_comap_left]
  exact profiniteClosure_comap_eq_of_closed fiveCutter
    (MatchedSubgroupAmalgam.bigInA edgeToP edgeToC) hfive

end PairedReturnFiveCutterProfiniteReduction
end Higman
end GroupApproximation
