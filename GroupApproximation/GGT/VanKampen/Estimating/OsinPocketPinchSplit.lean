import GroupApproximation.GGT.VanKampen.SurgeryPinchSplitDiagram
import GroupApproximation.GGT.VanKampen.SurgeryPinchSplitRegions
import GroupApproximation.GGT.VanKampen.PermOrbitJoinReach
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchUnpinched
import GroupApproximation.Meta.AxiomGuard

/-!
# A pocket face set across a vertex splitting

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  A pinched pocket face set passes twice through a vertex.  Surgery 3
(`PinchSplit.Input.diagram`) splits a vertex at two darts `x` and `y`, merging the two faces after
them.  When the face set avoids both merged faces, the split keeps every dart, every label, every
relator cell word and the exterior word, so the pocket face set transports by the identity on
darts, with the same boundary cycle, arcs and sides.

* `PinchSplit.Input.transportBoundaryCycle` and `transportBoundaryCycle_followsBoundary`: the
  boundary cycle of an avoiding face set is a boundary cycle after the split, and it still
  follows the boundary.  Face rotation changes only at `alpha x` and `alpha y`, in the merged
  faces, and vertex rotation only at `x` and `y`, which are not internal.
* `PocketFaceSet.pinchSplit`, `pinchSplit_boundary_cycle` and `pinchSplit_followsBoundary`: the
  transported pocket face set.
* `PinchSplit.Input.vertexOf_eq_of_diagram`: the split refines vertices.
* `PinchSplit.Input.sameCycle_x_of_stretch` and `sameCycle_y_of_stretch`: the new vertex of `x`
  contains the old stretch of vertex rotation that runs into `x` without passing `y`, and the
  same with `x` and `y` exchanged.
* `PinchSplit.Input.vertexOf_x_ne_y`: `x` and `y` lie on different vertices after the split.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- A stretch of `p` that runs into `a` without passing `b` stays in the cycle of `a` after
composing with the transposition of `a` and `b`. -/
private theorem sameCycle_mul_swap_of_pow_eq {α : Type*} [DecidableEq α] (p : Equiv.Perm α)
    (a b : α) (n : ℕ) :
    ∀ d : α, (p ^ n) d = a → (∀ i ≤ n, (p ^ i) d ≠ b) →
      (p * Equiv.swap a b).SameCycle d a := by
  induction n with
  | zero =>
      intro d hn _
      have hd : d = a := hn
      subst hd
      exact Equiv.Perm.SameCycle.refl _ _
  | succ n ih =>
      intro d hn hb
      by_cases hda : d = a
      · subst hda
        exact Equiv.Perm.SameCycle.refl _ _
      · have hdb : d ≠ b := hb 0 (Nat.zero_le _)
        have hstep : (p * Equiv.swap a b) d = p d := by
          rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hda hdb]
        have hn' : (p ^ n) (p d) = a := by
          rw [pow_succ, Equiv.Perm.mul_apply] at hn
          exact hn
        have hb' : ∀ i ≤ n, (p ^ i) (p d) ≠ b := fun i hi => by
          have h := hb (i + 1) (Nat.succ_le_succ hi)
          rw [pow_succ, Equiv.Perm.mul_apply] at h
          exact h
        have h := ih (p d) hn' hb'
        rw [← hstep] at h
        exact Equiv.Perm.sameCycle_apply_left.mp h

namespace PinchSplit.Input

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} [DecidableEq Delta.toCombMap.Dart] (I : Input Delta)

/-! ## Boundary cycles -/

/-- Vertex rotation is unchanged at a dart whose reverse is based in an avoiding face set. -/
theorem sigma_apply_of_alpha_mem {s : Finset Delta.toCombMap.Face} (hs : I.Avoids s)
    {d : Delta.toCombMap.Dart} (hd : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∈ s) :
    I.diagram.toCombMap.sigma d = Delta.toCombMap.sigma d := by
  have hx : d ≠ I.x := fun h => hs.1 (by subst h; exact hd)
  have hy : d ≠ I.y := fun h => hs.2 (by subst h; exact hd)
  change Delta.toCombMap.sigma (Equiv.swap I.x I.y d) = Delta.toCombMap.sigma d
  rw [Equiv.swap_apply_of_ne_of_ne hx hy]

/-- **The boundary cycle of a face set avoiding the pinch, after the split.** -/
noncomputable def transportBoundaryCycle {s : Finset Delta.toCombMap.Face} (hs : I.Avoids s)
    (B : Surgery.MapCollapse.BoundaryCycle Delta.toCombMap s) :
    Surgery.MapCollapse.BoundaryCycle I.diagram.toCombMap (I.faceSet s) where
  cycle := B.cycle
  cycle_nonempty := B.cycle_nonempty
  cycle_nodup := B.cycle_nodup
  cycle_mem_iff := fun d => (B.cycle_mem_iff d).trans (I.isBoundaryDart_iff hs d).symm

theorem transportBoundaryCycle_cycle {s : Finset Delta.toCombMap.Face} (hs : I.Avoids s)
    (B : Surgery.MapCollapse.BoundaryCycle Delta.toCombMap s) :
    (I.transportBoundaryCycle hs B).cycle = B.cycle :=
  rfl

/-- The boundary rotation of the transported cycle is the old boundary rotation. -/
theorem transportBoundaryCycle_boundaryPerm_val {s : Finset Delta.toCombMap.Face}
    (hs : I.Avoids s) (B : Surgery.MapCollapse.BoundaryCycle Delta.toCombMap s)
    (d : Surgery.MapCollapse.BoundaryDart I.diagram.toCombMap (I.faceSet s)) :
    ((I.transportBoundaryCycle hs B).boundaryPerm d).1 =
      (B.boundaryPerm ⟨d.1, (I.isBoundaryDart_iff hs d.1).mp d.2⟩).1 := by
  obtain ⟨i, rfl⟩ := (I.transportBoundaryCycle hs B).positionEquiv.surjective d
  have hB : (⟨((I.transportBoundaryCycle hs B).positionEquiv i).1,
      (I.isBoundaryDart_iff hs ((I.transportBoundaryCycle hs B).positionEquiv i).1).mp
        ((I.transportBoundaryCycle hs B).positionEquiv i).2⟩ :
        Surgery.MapCollapse.BoundaryDart Delta.toCombMap s) = B.positionEquiv i := by
    apply Subtype.ext
    exact Surgery.MapCollapse.positionEquiv_val I.diagram.toCombMap (I.faceSet s)
      (I.transportBoundaryCycle hs B) i
  rw [hB, Surgery.MapCollapse.boundaryPerm_positionEquiv_val,
    Surgery.MapCollapse.boundaryPerm_positionEquiv_val]
  rfl

/-- A step of the boundary walk, across an internal dart by vertex rotation, survives the
split. -/
theorem walkStep_transport {s : Finset Delta.toCombMap.Face} (hs : I.Avoids s)
    {a b : Delta.toCombMap.Dart}
    (hab : Surgery.MapCollapse.InternalDart Delta.toCombMap s a ∧ Delta.toCombMap.sigma a = b) :
    Surgery.MapCollapse.InternalDart I.diagram.toCombMap (I.faceSet s) a ∧
      I.diagram.toCombMap.sigma a = b :=
  ⟨⟨(I.faceOf_mem_faceSet_iff hs a).mpr hab.1.1,
    (I.faceOf_mem_faceSet_iff hs (Delta.toCombMap.alpha a)).mpr hab.1.2⟩,
    (I.sigma_apply_of_alpha_mem hs hab.1.2).trans hab.2⟩

/-- **The transported boundary cycle follows the boundary.** -/
theorem transportBoundaryCycle_followsBoundary {s : Finset Delta.toCombMap.Face}
    (hs : I.Avoids s) (B : Surgery.MapCollapse.BoundaryCycle Delta.toCombMap s)
    (h : B.FollowsBoundary) : (I.transportBoundaryCycle hs B).FollowsBoundary := by
  intro d
  have hd : Surgery.MapCollapse.IsBoundaryDart Delta.toCombMap s d.1 :=
    (I.isBoundaryDart_iff hs d.1).mp d.2
  have hwalk := h ⟨d.1, hd⟩
  unfold Surgery.MapCollapse.BoundaryWalk at hwalk ⊢
  rw [I.transportBoundaryCycle_boundaryPerm_val hs B d, I.facePerm_of_mem hs hd.1]
  exact hwalk.lift id fun _ _ hab => I.walkStep_transport hs hab

/-! ## Vertices -/

/-- **The split refines vertices.** -/
theorem vertexOf_eq_of_diagram {d e : Delta.toCombMap.Dart}
    (h : I.diagram.toCombMap.vertexOf d = I.diagram.toCombMap.vertexOf e) :
    Delta.toCombMap.vertexOf d = Delta.toCombMap.vertexOf e := by
  rw [CombMap.vertexOf_eq_iff] at h
  refine OrbitClassifier.eq_of_sameCycle I.diagram.toCombMap.sigma Delta.toCombMap.vertexOf
    (fun (z : Delta.toCombMap.Dart) => ?_) h
  have hz : Delta.toCombMap.sigma.SameCycle z (Equiv.swap I.x I.y z) := by
    by_cases hx : z = I.x
    · rw [hx, Equiv.swap_apply_left]
      exact I.same_vertex
    · by_cases hy : z = I.y
      · rw [hy, Equiv.swap_apply_right]
        exact I.same_vertex.symm
      · exact ⟨0, (Equiv.swap_apply_of_ne_of_ne hx hy).symm⟩
  rw [CombMap.vertexOf_eq_iff]
  change Delta.toCombMap.sigma.SameCycle (Delta.toCombMap.sigma (Equiv.swap I.x I.y z)) z
  exact Equiv.Perm.sameCycle_apply_left.mpr hz.symm

/-- **The stretch into `x`.**  The new vertex of `x` contains every old stretch of vertex
rotation that runs into `x` without passing `y`. -/
theorem sameCycle_x_of_stretch {d : Delta.toCombMap.Dart} {n : ℕ}
    (hn : (Delta.toCombMap.sigma ^ n) d = I.x)
    (hy : ∀ i ≤ n, (Delta.toCombMap.sigma ^ i) d ≠ I.y) :
    I.diagram.toCombMap.sigma.SameCycle d I.x :=
  sameCycle_mul_swap_of_pow_eq Delta.toCombMap.sigma I.x I.y n d hn hy

/-- **The stretch into `y`.**  The new vertex of `y` contains every old stretch of vertex
rotation that runs into `y` without passing `x`. -/
theorem sameCycle_y_of_stretch {d : Delta.toCombMap.Dart} {n : ℕ}
    (hn : (Delta.toCombMap.sigma ^ n) d = I.y)
    (hx : ∀ i ≤ n, (Delta.toCombMap.sigma ^ i) d ≠ I.x) :
    I.diagram.toCombMap.sigma.SameCycle d I.y := by
  have h := sameCycle_mul_swap_of_pow_eq Delta.toCombMap.sigma I.y I.x n d hn hx
  rw [Equiv.swap_comm] at h
  exact h

/-- **The two darts of the pinch lie on different vertices after the split.** -/
theorem vertexOf_x_ne_y :
    I.diagram.toCombMap.vertexOf I.x ≠ I.diagram.toCombMap.vertexOf I.y := by
  intro h
  rw [CombMap.vertexOf_eq_iff] at h
  have hxy : (Delta.toCombMap.sigma * Equiv.swap I.x I.y).SameCycle I.x I.y := h
  have hcard : Nat.card (CombMap.Orbit (Delta.toCombMap.sigma * Equiv.swap I.x I.y)) =
      Nat.card (CombMap.Orbit Delta.toCombMap.sigma) :=
    Nat.card_congr (Quotient.congrRight fun a b =>
      ⟨fun hab => (Delta.toCombMap.vertexOf_eq_iff a b).mp
          (I.vertexOf_eq_of_diagram ((I.diagram.toCombMap.vertexOf_eq_iff a b).mpr hab)),
        fun hab => PermCycleCoordinates.sameCycle_mul_swap_of_sameCycle _ _ _ hxy hab⟩)
  have hcount := I.vertexCount_eq
  change Nat.card (CombMap.Orbit (Delta.toCombMap.sigma * Equiv.swap I.x I.y)) =
    Nat.card (CombMap.Orbit Delta.toCombMap.sigma) + 1 at hcount
  rw [hcard] at hcount
  omega

end PinchSplit.Input

open Embedded

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}
  [DecidableEq X.toCombMap.Dart] {lo hi : ℕ}

/-- **The pocket face set after a vertex splitting** at a pinch avoiding its faces: the image
face set, the same cells through the order-preserving cell map, and the same boundary cycle,
arcs and sides. -/
noncomputable def pinchSplit (K : PocketFaceSet D eps X lo hi) (I : PinchSplit.Input X)
    (hs : I.Avoids K.faces) : PocketFaceSet D eps I.diagram lo hi where
  faces := I.faceSet K.faces
  outerFace_not_mem := by
    rw [I.diagram_outerFace]
    exact fun h => K.outerFace_not_mem ((I.kept_mem_faceSet_iff hs).mp h)
  source := I.cellMap.indexEquiv K.source
  source_not_mem := by
    rw [I.cellMap.indexed_cell, I.cellMap.face_eq]
    exact fun h => K.source_not_mem ((I.kept_mem_faceSet_iff hs).mp h)
  kept := I.cellMap.indexEquiv K.kept
  kept_mem := by
    rw [I.cellMap.indexed_cell, I.cellMap.face_eq]
    exact (I.kept_mem_faceSet_iff hs).mpr K.kept_mem
  sourceArc := K.sourceArc.mapTo id (I.cellDarts_eq K.source)
  targetArc := K.targetArc.mapTo id I.outerDarts_eq
  firstSide := K.firstSide
  secondSide := K.secondSide
  boundary := I.transportBoundaryCycle hs K.boundary
  decomposition := by
    have h1 : (K.sourceArc.mapTo id (I.cellDarts_eq K.source)).darts = K.sourceArc.darts :=
      (CyclicArc.mapTo_darts _ _ _).trans (List.map_id _)
    have h2 : (K.targetArc.mapTo id I.outerDarts_eq).darts = K.targetArc.darts :=
      (CyclicArc.mapTo_darts _ _ _).trans (List.map_id _)
    exact K.decomposition.trans (congrArg₂ (fun (a b : List X.toCombMap.Dart) =>
      K.firstSide ++ invDarts X a ++ K.secondSide ++ b) h1.symm h2.symm)
  firstSide_length_le := K.firstSide_length_le
  secondSide_length_le := K.secondSide_length_le
  firstSide_norm_le := K.firstSide_norm_le
  secondSide_norm_le := K.secondSide_norm_le
  lo_le := by
    rw [CyclicArc.mapTo_start]
    exact K.lo_le
  le_hi := by
    rw [CyclicArc.mapTo_start, CyclicArc.mapTo_length]
    exact K.le_hi

theorem pinchSplit_faces (K : PocketFaceSet D eps X lo hi) (I : PinchSplit.Input X)
    (hs : I.Avoids K.faces) : (K.pinchSplit I hs).faces = I.faceSet K.faces :=
  rfl

theorem pinchSplit_source (K : PocketFaceSet D eps X lo hi) (I : PinchSplit.Input X)
    (hs : I.Avoids K.faces) : (K.pinchSplit I hs).source = I.cellMap.indexEquiv K.source :=
  rfl

theorem pinchSplit_kept (K : PocketFaceSet D eps X lo hi) (I : PinchSplit.Input X)
    (hs : I.Avoids K.faces) : (K.pinchSplit I hs).kept = I.cellMap.indexEquiv K.kept :=
  rfl

/-- **The boundary cycle is unchanged.** -/
theorem pinchSplit_boundary_cycle (K : PocketFaceSet D eps X lo hi) (I : PinchSplit.Input X)
    (hs : I.Avoids K.faces) : (K.pinchSplit I hs).boundary.cycle = K.boundary.cycle :=
  rfl

theorem pinchSplit_firstSide (K : PocketFaceSet D eps X lo hi) (I : PinchSplit.Input X)
    (hs : I.Avoids K.faces) : (K.pinchSplit I hs).firstSide = K.firstSide :=
  rfl

theorem pinchSplit_secondSide (K : PocketFaceSet D eps X lo hi) (I : PinchSplit.Input X)
    (hs : I.Avoids K.faces) : (K.pinchSplit I hs).secondSide = K.secondSide :=
  rfl

theorem pinchSplit_sourceArc_darts (K : PocketFaceSet D eps X lo hi) (I : PinchSplit.Input X)
    (hs : I.Avoids K.faces) : (K.pinchSplit I hs).sourceArc.darts = K.sourceArc.darts :=
  (K.sourceArc.mapTo_darts id (I.cellDarts_eq K.source)).trans (List.map_id _)

theorem pinchSplit_targetArc_darts (K : PocketFaceSet D eps X lo hi) (I : PinchSplit.Input X)
    (hs : I.Avoids K.faces) : (K.pinchSplit I hs).targetArc.darts = K.targetArc.darts :=
  (K.targetArc.mapTo_darts id I.outerDarts_eq).trans (List.map_id _)

theorem pinchSplit_targetArc_start (K : PocketFaceSet D eps X lo hi) (I : PinchSplit.Input X)
    (hs : I.Avoids K.faces) : (K.pinchSplit I hs).targetArc.start.1 = K.targetArc.start.1 :=
  K.targetArc.mapTo_start id I.outerDarts_eq

/-- **The transported pocket face set follows the boundary.** -/
theorem pinchSplit_followsBoundary (K : PocketFaceSet D eps X lo hi) (I : PinchSplit.Input X)
    (hs : I.Avoids K.faces) (h : K.boundary.FollowsBoundary) :
    (K.pinchSplit I hs).boundary.FollowsBoundary :=
  I.transportBoundaryCycle_followsBoundary hs K.boundary h

end PocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.sigma_apply_of_alpha_mem
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.transportBoundaryCycle
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.transportBoundaryCycle_cycle
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.transportBoundaryCycle_boundaryPerm_val
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.walkStep_transport
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.transportBoundaryCycle_followsBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.vertexOf_eq_of_diagram
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.sameCycle_x_of_stretch
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.sameCycle_y_of_stretch
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.vertexOf_x_ne_y
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplit
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplit_faces
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplit_source
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplit_kept
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplit_boundary_cycle
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplit_firstSide
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplit_secondSide
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplit_sourceArc_darts
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplit_targetArc_darts
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplit_targetArc_start
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplit_followsBoundary
