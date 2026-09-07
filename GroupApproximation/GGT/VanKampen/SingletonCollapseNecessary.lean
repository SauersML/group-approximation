import GroupApproximation.GGT.VanKampen.SingletonFaceBoundary
import GroupApproximation.Meta.AxiomGuard

/-! # Exact singleton collapse boundaries exclude internally paired darts -/

namespace GroupApproximation.GGT.VanKampen.Surgery.MapCollapse

universe v

/-- Every dart of the stored face boundary must cross out of the singleton
region. In particular, an edge cannot have the face on both sides. -/
theorem BoundaryCycle.noInternalFaceDart_of_cycle_eq
    {M : CombMap.{v}} {f : M.Face} (boundary : BoundaryCycle M {f})
    (B : FaceBoundary M f) (hcycle : boundary.cycle = B.darts) :
    NoInternalFaceDart M f := by
  intro d hd ha
  have hmem : d ∈ boundary.cycle := by
    rw [hcycle]
    exact (B.mem_iff d).mpr hd
  exact ((boundary.cycle_mem_iff d).mp hmem).2 (Finset.mem_singleton.mpr ha)

end GroupApproximation.GGT.VanKampen.Surgery.MapCollapse

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.noInternalFaceDart_of_cycle_eq
