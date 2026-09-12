import GroupApproximation.GGT.VanKampen.PermFirstReturnOrbits
import GroupApproximation.GGT.VanKampen.CyclicFaceBoundary
import GroupApproximation.GGT.VanKampen.SurgeryReclosedFaces
import GroupApproximation.GGT.VanKampen.SurgeryFaceNew

/-!
# Vertices of a region collapse along its genuine boundary walk

For the genuine boundary walk, each reclosed vertex step is the first return
of the old vertex rotation to retained darts. Thus reclosed vertices are
exactly the original vertices incident to at least one retained dart. Neither
connectedness nor Euler preservation is an input. An arbitrary ordering of
the boundary darts need not satisfy this boundary-walk condition.
-/

namespace GroupApproximation.GGT.VanKampen.Surgery.MapCollapse

open Equiv
universe v

/-- Advance around a selected face, then skip only internal darts. Crossing
an internal edge and advancing around its other face is old vertex rotation. -/
def BoundaryWalk (M : CombMap.{v}) (faces : Finset M.Face) (d e : M.Dart) : Prop :=
  Relation.ReflTransGen (fun x y => InternalDart M faces x ∧ M.sigma x = y)
    (M.facePerm d) e

/-- The supplied cyclic enumeration follows the actual face-set boundary. -/
def BoundaryCycle.FollowsBoundary {M : CombMap.{v}} {faces : Finset M.Face}
    (boundary : BoundaryCycle M faces) : Prop :=
  ∀ d : BoundaryDart M faces,
    BoundaryWalk M faces d.1 (boundary.boundaryPerm d).1

/-- The usual chain and closing step imply the boundary-rotation condition. -/
theorem BoundaryCycle.followsBoundary_of_chain {M : CombMap.{v}}
    {faces : Finset M.Face} (boundary : BoundaryCycle M faces)
    (hchain : boundary.cycle.IsChain (BoundaryWalk M faces))
    (hclose : BoundaryWalk M faces (boundary.cycle.getLast boundary.cycle_nonempty)
      (boundary.cycle.head boundary.cycle_nonempty)) : boundary.FollowsBoundary := by
  intro d
  obtain ⟨i, rfl⟩ := boundary.positionEquiv.surjective d
  rw [positionEquiv_val, boundaryPerm_positionEquiv_val]
  exact FaceBoundary.cyclic_relation_get_rotate (BoundaryWalk M faces)
    boundary.cycle boundary.cycle_nonempty hchain hclose i

/-- Reclosed vertex rotation is precisely the first return of old rotation. -/
theorem reclosed_sigma_firstReturn (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) (hwalk : boundary.FollowsBoundary) :
    PermFirstReturn.IsFirstReturn M.sigma (reclosedMap M faces boundary).sigma
      (Function.Embedding.subtype _) := by
  intro d
  let N := reclosedMap M faces boundary
  have hsig : (N.facePerm (N.alpha d)).1 = (N.sigma d).1 := by
    change (N.sigma (N.alpha (N.alpha d))).1 = (N.sigma d).1
    rw [N.alpha_involutive d]
  have hold : M.facePerm (N.alpha d).1 = M.sigma d.1 := by
    change M.sigma (M.alpha (M.alpha d.1)) = M.sigma d.1
    rw [M.alpha_involutive d.1]
  by_cases hf : M.faceOf (N.alpha d).1 ∈ faces
  · let b : BoundaryDart M faces :=
      ⟨(N.alpha d).1, isBoundaryDart_of_mem M faces (N.alpha d) hf⟩
    have hs := reclosedMap_facePerm_val_of_mem M faces boundary (N.alpha d) hf
    have hpath := hwalk b
    change Relation.ReflTransGen
      (fun x y => InternalDart M faces x ∧ M.sigma x = y)
      (M.facePerm (N.alpha d).1) (boundary.boundaryPerm b).1 at hpath
    rw [hold] at hpath
    obtain ⟨n, hn, hskip⟩ := PermFirstReturn.exists_pow_of_skip_walk
      M.sigma (InternalDart M faces) hpath
    refine ⟨n + 1, by omega, ?_, ?_⟩
    · change (M.sigma ^ (n + 1)) d.1 = (N.sigma d).1
      rw [pow_succ, Perm.mul_apply, hn]
      exact hs.symm.trans hsig
    · intro k hk hkn hkept
      obtain ⟨c, hc⟩ := hkept
      have hi := hskip (k - 1) (by omega)
      have heq : (M.sigma ^ (k - 1)) (M.sigma d.1) = (M.sigma ^ k) d.1 := by
        rw [← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel hk]
      rw [heq] at hi
      have hc' : c.1 = (M.sigma ^ k) d.1 := hc
      rw [← hc'] at hi
      exact c.property hi
  · have hs := reclosedMap_facePerm_val_of_notMem M faces boundary (N.alpha d) hf
    refine ⟨1, by omega, ?_, by intro k hk hkn; omega⟩
    change (M.sigma ^ 1) d.1 = (N.sigma d).1
    simpa only [pow_one, hold] using hs.symm.trans hsig

/-- Two retained darts meet at a new vertex exactly when they met at an old
vertex. This also handles old rotation cycles containing deleted darts. -/
theorem reclosed_vertexOf_eq_iff (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) (hwalk : boundary.FollowsBoundary)
    (d e : KeptDart M faces) :
    (reclosedMap M faces boundary).vertexOf d =
        (reclosedMap M faces boundary).vertexOf e ↔ M.vertexOf d.1 = M.vertexOf e.1 := by
  rw [CombMap.vertexOf_eq_iff, M.vertexOf_eq_iff]
  exact PermFirstReturn.sameCycle_iff _ _ _
    (reclosed_sigma_firstReturn M faces boundary hwalk) d e

/-- Actual vertices after deletion are the old vertices incident to a kept
dart. Entirely deleted vertices are excluded by this explicit predicate. -/
noncomputable def reclosedVertexEquiv (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) (hwalk : boundary.FollowsBoundary) :
    (reclosedMap M faces boundary).Vertex ≃
      {c : M.Vertex // ∃ d : KeptDart M faces, M.vertexOf d.1 = c} :=
  PermFirstReturn.orbitEquiv M.sigma (reclosedMap M faces boundary).sigma
    (Function.Embedding.subtype _) (reclosed_sigma_firstReturn M faces boundary hwalk)

/-- The vertex count is derived from the actual boundary walk. -/
theorem reclosedMap_vertexCount (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) (hwalk : boundary.FollowsBoundary) :
    (reclosedMap M faces boundary).vertexCount =
      Nat.card {c : M.Vertex // ∃ d : KeptDart M faces, M.vertexOf d.1 = c} :=
  Nat.card_congr (reclosedVertexEquiv M faces boundary hwalk)

end GroupApproximation.GGT.VanKampen.Surgery.MapCollapse

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.reclosed_sigma_firstReturn
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.reclosedVertexEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.reclosedMap_vertexCount
