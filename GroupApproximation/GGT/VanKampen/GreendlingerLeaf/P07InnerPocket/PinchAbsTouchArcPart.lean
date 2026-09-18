import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsTouchArcLemmas
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsTouchNIParts
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-77: the arc clauses from the residual predicate

Let `ow` be the outside walk of an `EnclosedFaceSetSucc` and `A₀` an arc of a relator cell.
`pinchAbsTouchArc_arc_of_run` proves the two arc clauses of `pinchCut_Tail` for `A₀` from
`pinchAbsTouchArc_Run X.toCombMap A₀.darts ow`:
* (i) a run `U` of `invDarts X ow` inside `invDarts X A₀` that stops before the end is the
  reverse of an arc;
* (ii) if `invDarts X ow` lies inside `invDarts X A₀`, some rotation of `ow` is an arc.

Proof of (i).  `invDarts X` turns the rotation of `invDarts X ow` into a rotation of `ow`, namely
`ow.rotate m' = invDarts X V ++ invDarts X U`.  Every adjacent pair of `invDarts X U` is on the
face of the cell, so `pinchAbsTouchArc_step` makes it a face step.  The residual case is covered by
`Run` (i), since `V` has a dart off `invDarts X A₀`.  So `invDarts X U` is a duplicate-free face
chain of cell darts, hence an arc (`PocketRun.exists_cyclicArc_of_isChain`).  Proof of (ii): the
same, for the rotation that `Run` (ii) names.

`pinchAbsTouchArc_arcPart_of_run` assembles lane gl-p07-76's `pinchAbsTouchNI_ArcPart`
(clauses 5–8 of `pinchCut_Tail`, verbatim).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W}

/-- A dart of an arc of a relator cell lies on the face of the cell. -/
theorem pinchAbsTouchArc_face_of_mem {i : Fin X.rCellCount} (A : CyclicArc (cellDarts X i))
    {x : X.toCombMap.Dart} (hx : x ∈ A.darts) :
    X.toCombMap.faceOf x = (Embedded.cell X i).face :=
  ((X.faceBoundary (Embedded.cell X i).face).mem_iff x).mp (A.mem_cycle_of_mem_darts hx)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchArc_face_of_mem

/-- **Clause (i) for one arc.** -/
theorem pinchAbsTouchArc_run_arc {i : Fin X.rCellCount} {F : Finset X.toCombMap.Face}
    {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow)
    (A₀ : CyclicArc (cellDarts X i)) (hR : pinchAbsTouchArc_Run X.toCombMap A₀.darts ow)
    (m : ℕ) (U V : List X.toCombMap.Dart) (hmUV : (invDarts X ow).rotate m = U ++ V)
    (hU : ∀ e ∈ U, e ∈ invDarts X A₀.darts) (hV : ∃ e ∈ V, e ∉ invDarts X A₀.darts) :
    ∃ A : CyclicArc (cellDarts X i), U = invDarts X A.darts := by
  have h0 : List.IsRotated (invDarts X ow) ((invDarts X ow).rotate m) := ⟨m, rfl⟩
  have hrot : List.IsRotated (invDarts X (invDarts X ow))
      (invDarts X ((invDarts X ow).rotate m)) := h0.reverse.map X.toCombMap.alpha
  rw [pinchAbsTouchArc_invInv, hmUV, pinchAbsTouchArc_invAppend] at hrot
  obtain ⟨m', hm'⟩ := hrot
  have hmemA : ∀ x ∈ invDarts X U, x ∈ A₀.darts := fun x hx =>
    (pinchAbsTouchArc_mem_inv X _ _).mp
      (hU _ ((pinchAbsTouchArc_mem_inv X _ _).mp hx))
  obtain ⟨e, heV, heA⟩ := hV
  have hoff : ∃ d ∈ ow, d ∉ A₀.darts := by
    refine ⟨X.toCombMap.alpha e, ?_, fun h => heA ((pinchAbsTouchArc_mem_inv X _ _).mpr h)⟩
    have h1 : X.toCombMap.alpha e ∈ ow.rotate m' := by
      rw [hm']
      exact List.mem_append_left _ ((pinchAbsTouchArc_alpha_mem_inv X _ _).mpr heV)
    exact List.mem_rotate.mp h1
  have hchain : (invDarts X U).IsChain fun d e => X.toCombMap.facePerm d = e := by
    refine List.isChain_iff_forall_rel_of_append_cons_cons.mpr ?_
    intro x y l₁ l₂ hsplit
    have hrot' : ow.rotate m' = (invDarts X V ++ l₁) ++ x :: y :: l₂ := by
      rw [hm', hsplit, List.append_assoc]
    have hx : x ∈ A₀.darts := hmemA x (by rw [hsplit]; simp)
    have hy : y ∈ A₀.darts := hmemA y (by rw [hsplit]; simp)
    exact pinchAbsTouchArc_step E hrot'
      ((pinchAbsTouchArc_face_of_mem A₀ hy).trans (pinchAbsTouchArc_face_of_mem A₀ hx).symm)
      (hR.1 hoff m' _ _ x y hrot' hx hy)
  have hnd : (invDarts X U).Nodup := by
    have h1 : (invDarts X V ++ invDarts X U).Nodup := by
      rw [← hm']
      exact List.nodup_rotate.mpr E.nodup
    exact h1.of_append_right
  obtain ⟨A, hA⟩ : ∃ A : CyclicArc (cellDarts X i), A.darts = invDarts X U :=
    PocketRun.exists_cyclicArc_of_isChain (X.faceBoundary (Embedded.cell X i).face)
      (invDarts X U) hnd (fun x hx => A₀.mem_cycle_of_mem_darts (hmemA x hx)) hchain
  exact ⟨A, by rw [hA, pinchAbsTouchArc_invInv]⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchArc_run_arc

/-- **Clause (ii) for one arc.** -/
theorem pinchAbsTouchArc_run_all {i : Fin X.rCellCount} {F : Finset X.toCombMap.Face}
    {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow)
    (A₀ : CyclicArc (cellDarts X i)) (hR : pinchAbsTouchArc_Run X.toCombMap A₀.darts ow)
    (hall : ∀ e ∈ invDarts X ow, e ∈ invDarts X A₀.darts) :
    ∃ (n : ℕ) (A : CyclicArc (cellDarts X i)), invDarts X (ow.rotate n) = invDarts X A.darts := by
  have hallG : ∀ d ∈ ow, d ∈ A₀.darts := fun d hd =>
    (pinchAbsTouchArc_alpha_mem_inv X _ _).mp
      (hall _ ((pinchAbsTouchArc_alpha_mem_inv X _ _).mpr hd))
  obtain ⟨n, hn⟩ := hR.2 hallG
  have hmemA : ∀ x ∈ ow.rotate n, x ∈ A₀.darts := fun x hx => hallG x (List.mem_rotate.mp hx)
  have hchain : (ow.rotate n).IsChain fun d e => X.toCombMap.facePerm d = e := by
    refine List.isChain_iff_forall_rel_of_append_cons_cons.mpr ?_
    intro x y l₁ l₂ hsplit
    have hx : x ∈ A₀.darts := hmemA x (by rw [hsplit]; simp)
    have hy : y ∈ A₀.darts := hmemA y (by rw [hsplit]; simp)
    exact pinchAbsTouchArc_step E hsplit
      ((pinchAbsTouchArc_face_of_mem A₀ hy).trans (pinchAbsTouchArc_face_of_mem A₀ hx).symm)
      (hn l₁ l₂ x y hsplit)
  obtain ⟨A, hA⟩ : ∃ A : CyclicArc (cellDarts X i), A.darts = ow.rotate n :=
    PocketRun.exists_cyclicArc_of_isChain (X.faceBoundary (Embedded.cell X i).face)
      (ow.rotate n) (List.nodup_rotate.mpr E.nodup)
      (fun x hx => A₀.mem_cycle_of_mem_darts (hmemA x hx)) hchain
  exact ⟨n, A, by rw [hA]⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchArc_run_all

/-- **The arc part from the residual predicate for both arcs.**  The conclusion is lane
gl-p07-76's `pinchAbsTouchNI_ArcPart`, clauses 5–8 of `pinchCut_Tail`, verbatim. -/
theorem pinchAbsTouchArc_arcPart_of_run {i j : Fin X.rCellCount} {F : Finset X.toCombMap.Face}
    {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j))
    (hR₁ : pinchAbsTouchArc_Run X.toCombMap G₁.darts ow)
    (hR₂ : pinchAbsTouchArc_Run X.toCombMap G₂.darts ow) :
    pinchAbsTouchNI_ArcPart G₁ G₂ ow :=
  ⟨pinchAbsTouchArc_run_arc E G₁ hR₁, pinchAbsTouchArc_run_all E G₁ hR₁,
    pinchAbsTouchArc_run_arc E G₂ hR₂, pinchAbsTouchArc_run_all E G₂ hR₂⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchArc_arcPart_of_run

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
