import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalResidual
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece08.Absorb
import GroupApproximation.Meta.AxiomGuard

/-!
# Unconditional clauses of the in-order block statement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-13.

Four clauses of `P10ExtremalResidual.ExtremalBlockClauses` follow from the others by pure
combinatorics, for an arbitrary region `r`:

* `outerAvoid_of_keptTarget`: if some dart of `K.targetArc` is kept by the move at `r`, the
  region of `r` avoids the exterior face (across a target dart lies the exterior face, and a kept
  dart has neither side in the region).
* `source_not_mem_flipFaces_of_keptSource`: if some dart of `K.sourceArc` is kept, the source face
  is not flipped (the source face lies outside `K.faces` and a kept dart is outside the region).
* `filter_keptPred_ne_nil`: if the region avoids the exterior face and the kept face is flipped,
  some dart of `K.boundary.cycle` is kept (a nonempty face set away from the exterior face has a
  boundary dart, `Piece08.exists_boundaryDart`, and the boundary darts after the move are the
  kept darts of the cycle, `isBoundaryDart_flipFaces_iff`).
* `isChain_invDarts_block`, `isChain_targetArc_block`: in a pocket in walk order, a contiguous
  block of `K.sourceArc` (read backwards) or of `K.targetArc` is a walk, as an infix of the walk
  `K.boundary.cycle`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section Lemmas

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A kept target dart keeps the region off the exterior face.** -/
theorem outerAvoid_of_keptTarget (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart)
    {e : X.toCombMap.Dart} (he : e ∈ K.targetArc.darts)
    (hk : P10ExtremalResidual.keptPred K r e = true) :
    ∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x := by
  intro x hx hrx
  have hsame := (X.toCombMap.faceOf_eq_iff (X.toCombMap.alpha e) x).mp
    ((P10Rose.FilterMove.faceOf_alpha_of_mem_targetArc K he).trans hx.symm)
  have hre : Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r
      (X.toCombMap.alpha e) :=
    Relation.EqvGen.trans _ _ _ hrx (Relation.EqvGen.symm _ _
      (eqvGen_faceClass_of_sameCycle X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) hsame))
  have h2 := ((movePred_eq_true_iff X.toCombMap
    (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) e).mp hk).2
  rw [(regionColour_eq_true_iff X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r
    (X.toCombMap.alpha e)).mpr hre] at h2
  exact absurd h2 (by decide)

/-- **A kept source dart keeps the source face unflipped.** -/
theorem source_not_mem_flipFaces_of_keptSource (K : PocketFaceSet D eps X lo hi)
    (r : X.toCombMap.Dart) {e : X.toCombMap.Dart} (he : e ∈ K.sourceArc.darts)
    (hk : P10ExtremalResidual.keptPred K r e = true) :
    (cell X K.source).face ∉ flipFaces X.toCombMap K.faces
      (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) := by
  have hfe : X.toCombMap.faceOf e = (cell X K.source).face :=
    ((X.faceBoundary (cell X K.source).face).mem_iff e).mp
      (K.sourceArc.mem_cycle_of_mem_darts he)
  intro hmem
  rw [← hfe] at hmem
  have h := (mem_flipFaces_iff (regionColour_step X.toCombMap
    (walkKeep X.toCombMap K.boundary.cycle) r) e).mp hmem
  rw [hfe] at h
  exact K.source_not_mem (h.mpr ((movePred_eq_true_iff X.toCombMap
    (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) e).mp hk).1)

/-- **The kept darts are nonempty** once the region avoids the exterior face and the kept face is
flipped. -/
theorem filter_keptPred_ne_nil (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart)
    (kept : Fin X.rCellCount)
    (hrout : ∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x)
    (hkept : (cell X kept).face ∈ flipFaces X.toCombMap K.faces
      (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r)) :
    K.boundary.cycle.filter (P10ExtremalResidual.keptPred K r) ≠ [] := by
  have hz := regionColour_step X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r
  have hout : X.outerFace ∉ flipFaces X.toCombMap K.faces
      (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) :=
    not_mem_flipFaces hz K.outerFace_not_mem fun x hx =>
      regionColour_eq_false X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) (hrout x hx)
  obtain ⟨d, hd⟩ := Piece08.exists_boundaryDart _ hout hkept
  have hdc := (isBoundaryDart_flipFaces_iff K.boundary.cycle_mem_iff hz
    (regionColour_indep K.boundary.cycle_mem_iff r) d).mp hd
  exact List.ne_nil_of_mem (List.mem_filter.mpr hdc)

/-- **A contiguous block of the reversed source arc is a walk.** -/
theorem isChain_invDarts_block (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    {pre mid post : List X.toCombMap.Dart} (hs : K.sourceArc.darts = pre ++ mid ++ post) :
    (invDarts X mid).IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e := by
  have hc : K.boundary.cycle.IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e := And.left hK
  rw [K.decomposition] at hc
  refine hc.left_of_append.left_of_append.right_of_append.infix
    ⟨invDarts X post, invDarts X pre, ?_⟩
  simp only [hs, invDarts, List.reverse_append, List.map_append, List.append_assoc]

/-- **A contiguous block of the target arc is a walk.** -/
theorem isChain_targetArc_block (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    {pre mid post : List X.toCombMap.Dart} (hs : K.targetArc.darts = pre ++ mid ++ post) :
    mid.IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e := by
  have hc : K.boundary.cycle.IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e := And.left hK
  rw [K.decomposition] at hc
  exact hc.right_of_append.infix ⟨pre, post, hs.symm⟩

end Lemmas

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock.outerAvoid_of_keptTarget
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock.source_not_mem_flipFaces_of_keptSource
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock.filter_keptPred_ne_nil
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock.isChain_invDarts_block
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalBlock.isChain_targetArc_block
