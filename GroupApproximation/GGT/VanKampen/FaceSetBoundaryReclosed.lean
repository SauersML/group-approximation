import GroupApproximation.GGT.VanKampen.SurgeryReclosedVertices
import GroupApproximation.GGT.VanKampen.Estimating.Embedded

/-!
# Reclosed vertices from the existing embedded face-set boundary

The chain and closing walk already stored in an embedded `FaceSetBoundary`
give the genuine map boundary walk. The reclosed vertex equivalence is then
constructed by the first-return theorem; no additional orbit hypothesis is
required of the contiguity region.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded

open Surgery.MapCollapse
universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} {faces : Finset Delta.toCombMap.Face}

/-- Existing elementary boundary moves are precisely internal vertex steps. -/
theorem internalBoundaryMove_to_skip {d e : Delta.toCombMap.Dart}
    (h : InternalBoundaryMove Delta faces d e) :
    InternalDart Delta.toCombMap faces d ∧ Delta.toCombMap.sigma d = e := by
  refine ⟨⟨h.1, h.2.1⟩, ?_⟩
  have he := h.2.2.symm
  change Delta.toCombMap.sigma (Delta.toCombMap.alpha (Delta.toCombMap.alpha d)) = e at he
  rw [Delta.toCombMap.alpha_involutive d] at he
  exact he

theorem boundaryStep_to_walk {d e : Delta.toCombMap.Dart}
    (h : BoundaryStep Delta faces d e) : BoundaryWalk Delta.toCombMap faces d e := by
  have hpath := h.2.2
  clear h
  induction hpath with
  | refl => exact .refl
  | tail _ hstep ih => exact .tail ih (internalBoundaryMove_to_skip hstep)

/-- Forget labels while retaining the literal cyclic enumeration. -/
def FaceSetBoundary.mapBoundaryCycle (B : FaceSetBoundary Delta faces) :
    BoundaryCycle Delta.toCombMap faces where
  cycle := B.cycle
  cycle_nonempty := B.cycle_nonempty
  cycle_nodup := B.cycle_nodup
  cycle_mem_iff := B.cycle_mem_iff

/-- The historical embedded record supplies the actual first-return walk. -/
theorem FaceSetBoundary.mapBoundaryCycle_follows (B : FaceSetBoundary Delta faces) :
    B.mapBoundaryCycle.FollowsBoundary := by
  apply BoundaryCycle.followsBoundary_of_chain
  · exact B.cycle_chain.imp fun _ _ h => boundaryStep_to_walk h
  · exact boundaryStep_to_walk B.cycle_closes

/-- Vertices after collapsing this embedded region are constructed directly
from its existing boundary walk, without a disc-certificate input. -/
noncomputable def FaceSetBoundary.reclosedVertexEquiv (B : FaceSetBoundary Delta faces) :
    (reclosedMap Delta.toCombMap faces B.mapBoundaryCycle).Vertex ≃
      {c : Delta.toCombMap.Vertex //
        ∃ d : KeptDart Delta.toCombMap faces, Delta.toCombMap.vertexOf d.1 = c} :=
  Surgery.MapCollapse.reclosedVertexEquiv _ _ _ B.mapBoundaryCycle_follows

end GroupApproximation.GGT.VanKampen.Embedded

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.FaceSetBoundary.mapBoundaryCycle_follows
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.FaceSetBoundary.reclosedVertexEquiv
