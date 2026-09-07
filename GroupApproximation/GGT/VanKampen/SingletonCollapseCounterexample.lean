import GroupApproximation.GGT.VanKampen.SingletonCollapseNecessary
import GroupApproximation.GGT.VanKampen.ExteriorArcCounterexample

/-!
# The unrestricted singleton relator-face producer is false

The existing six-dart planar diagram has a bridge with both darts on its
relator face. The singleton region's boundary excludes that internal edge,
so it cannot equal the complete stored face boundary. The original producer
and its conditional consumers remain unchanged.
-/

namespace GroupApproximation.GGT.VanKampen.SingletonCollapseCounterexample

open Surgery.MapCollapse ExteriorArcCounterexample

/-- The bridge's two orientations lie on the same listed relator face. -/
theorem bridge_both_sides :
    M.faceOf (0 : Fin 6) = relatorCell.face ∧
      M.faceOf (M.alpha (0 : Fin 6)) = relatorCell.face := by
  constructor
  · exact (faceOf_eq_face 0 0).mpr rfl
  · exact (faceOf_eq_face 1 0).mpr rfl

/-- Even the boundary part of the advertised singleton region is impossible. -/
theorem no_exact_singleton_region :
    ¬ ∃ region : IsDiscRegion diagram.toCombMap {relatorCell.face},
      region.toBoundaryCycle.cycle = (diagram.faceBoundary relatorCell.face).darts := by
  rintro ⟨region, hcycle⟩
  have hno := region.toBoundaryCycle.noInternalFaceDart_of_cycle_eq
    (diagram.faceBoundary relatorCell.face) hcycle
  exact hno 0 bridge_both_sides.1 bridge_both_sides.2

/-- The omitted local no-internal-edge condition is necessary even for
actual finite planar disc diagrams and their listed relator cells. -/
theorem not_relatorFaceSingletonProducer :
    ¬ RelatorFaceSingletonProducer (W := W) := by
  intro h
  exact no_exact_singleton_region (h diagram relatorCell (List.mem_singleton_self _))

end GroupApproximation.GGT.VanKampen.SingletonCollapseCounterexample

#audit_closed_axioms GroupApproximation.GGT.VanKampen.SingletonCollapseCounterexample.no_exact_singleton_region
#audit_closed_axioms GroupApproximation.GGT.VanKampen.SingletonCollapseCounterexample.not_relatorFaceSingletonProducer
