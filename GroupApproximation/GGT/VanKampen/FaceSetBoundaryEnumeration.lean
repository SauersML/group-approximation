import GroupApproximation.GGT.VanKampen.FaceSetBoundaryCircuits

/-!
# The finite family of actual face-set boundary circuits

The constructed successor gives a finite orbit type and a nonempty ordered
dart list for every orbit. These lists are disjoint, cover exactly the
boundary darts, and follow the actual boundary walk. Their total length is
the boundary-dart count. A single orbit therefore produces the historical
boundary and disc-region records with their walk and topology fields proved.
-/

namespace GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.FaceSetCircuits

open Equiv
open scoped BigOperators
universe v
variable (M : CombMap.{v}) (faces : Finset M.Face)

abbrev Component := CombMap.Orbit (boundaryPerm M faces)

noncomputable def circuit (c : Component M faces) : List M.Dart := by
  classical
  exact (closedOrbitList (boundaryPerm M faces) c.out).map Subtype.val

theorem circuit_nonempty (c : Component M faces) : circuit M faces c ≠ [] := by
  classical
  intro h
  exact closedOrbitList.nonempty (boundaryPerm M faces) c.out (List.map_eq_nil_iff.mp h)

theorem circuit_nodup (c : Component M faces) : (circuit M faces c).Nodup := by
  classical
  exact (closedOrbitList.nodup (boundaryPerm M faces) c.out).map Subtype.val_injective

/-- Exact membership retains both the boundary predicate and its component. -/
theorem mem_circuit_iff (c : Component M faces) (d : M.Dart) :
    d ∈ circuit M faces c ↔
      ∃ h : IsBoundaryDart M faces d, (Quotient.mk'' ⟨d, h⟩ : Component M faces) = c := by
  classical
  constructor
  · intro h
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
    have hsame := (closedOrbitList.mem_iff_sameCycle (boundaryPerm M faces) c.out b).mp hb
    exact ⟨b.2, (Quotient.sound hsame.symm).trans (Quotient.out_eq c)⟩
  · rintro ⟨hd, hc⟩
    apply List.mem_map.mpr
    refine ⟨⟨d, hd⟩, ?_, rfl⟩
    apply (closedOrbitList.mem_iff_sameCycle (boundaryPerm M faces) c.out _).mpr
    exact Quotient.exact ((Quotient.out_eq c).trans hc.symm)

/-- Each oriented boundary dart belongs to exactly one constructed circuit. -/
theorem existsUnique_circuit_iff (d : M.Dart) :
    (∃! c : Component M faces, d ∈ circuit M faces c) ↔ IsBoundaryDart M faces d := by
  constructor
  · rintro ⟨c, hc, _⟩
    exact (mem_circuit_iff M faces c d).mp hc |>.choose
  · intro hd
    refine ⟨Quotient.mk'' ⟨d, hd⟩, (mem_circuit_iff M faces _ d).mpr ⟨hd, rfl⟩, ?_⟩
    intro c hc
    obtain ⟨_, heq⟩ := (mem_circuit_iff M faces c d).mp hc
    exact heq.symm

theorem circuits_disjoint {c c' : Component M faces} (hne : c ≠ c') :
    List.Disjoint (circuit M faces c) (circuit M faces c') := by
  intro d hd hd'
  obtain ⟨h, hc⟩ := (mem_circuit_iff M faces c d).mp hd
  obtain ⟨h', hc'⟩ := (mem_circuit_iff M faces c' d).mp hd'
  exact hne (hc.symm.trans hc')

theorem circuit_chain (c : Component M faces) :
    (circuit M faces c).IsChain (BoundaryWalk M faces) := by
  classical
  rw [circuit, List.isChain_map]
  apply (closedOrbitList.chain (boundaryPerm M faces) c.out).imp
  intro a b hab
  rw [← hab]
  exact boundaryPerm_walk M faces a

theorem circuit_closes (c : Component M faces) :
    BoundaryWalk M faces ((circuit M faces c).getLast (circuit_nonempty M faces c))
      ((circuit M faces c).head (circuit_nonempty M faces c)) := by
  classical
  change BoundaryWalk M faces
    (((closedOrbitList (boundaryPerm M faces) c.out).map Subtype.val).getLast _)
    (((closedOrbitList (boundaryPerm M faces) c.out).map Subtype.val).head _)
  rw [List.getLast_map, List.head_map]
  rw [← closedOrbitList.closes (boundaryPerm M faces) c.out]
  exact boundaryPerm_walk M faces _

theorem circuit_length (c : Component M faces) :
    (circuit M faces c).length = CombMap.orbitDegree (boundaryPerm M faces) c := by
  classical
  rw [circuit, List.length_map, closedOrbitList.length_eq_orbitDegree]
  exact congrArg (CombMap.orbitDegree (boundaryPerm M faces)) (Quotient.out_eq c)

/-- The boundary circuits partition the original oriented perimeter exactly. -/
theorem sum_circuit_lengths :
    ∑ c : Component M faces, (circuit M faces c).length = Nat.card (BoundaryDart M faces) := by
  classical
  simp only [circuit_length]
  exact CombMap.sum_orbitDegree (boundaryPerm M faces)

/-- When the actual successor has one orbit, its list is the required full
boundary cycle. No boundary list or walk is supplied. -/
noncomputable def toBoundaryCycle (c : Component M faces)
    (hall : ∀ d : BoundaryDart M faces, (Quotient.mk'' d : Component M faces) = c) :
    BoundaryCycle M faces where
  cycle := circuit M faces c
  cycle_nonempty := circuit_nonempty M faces c
  cycle_nodup := circuit_nodup M faces c
  cycle_mem_iff d := by
    rw [mem_circuit_iff]
    exact ⟨fun h => h.choose, fun h => ⟨h, hall ⟨d, h⟩⟩⟩

theorem toBoundaryCycle_follows (c : Component M faces)
    (hall : ∀ d : BoundaryDart M faces, (Quotient.mk'' d : Component M faces) = c) :
    (toBoundaryCycle M faces c hall).FollowsBoundary :=
  BoundaryCycle.followsBoundary_of_chain _ (circuit_chain M faces c) (circuit_closes M faces c)

/-- A single constructed boundary circuit in a planar source constructs the
disc-region topology used by the cut operation. -/
noncomputable def toDiscRegion (c : Component M faces)
    (hall : ∀ d : BoundaryDart M faces, (Quotient.mk'' d : Component M faces) = c)
    (hM : M.IsPlanar) : IsDiscRegion M faces :=
  (toBoundaryCycle M faces c hall).toDiscRegion_of_followsBoundary M faces
    (toBoundaryCycle_follows M faces c hall) hM

end GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.FaceSetCircuits

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.FaceSetCircuits.existsUnique_circuit_iff
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.FaceSetCircuits.sum_circuit_lengths
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.FaceSetCircuits.toDiscRegion
