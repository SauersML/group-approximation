import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickRun
import GroupApproximation.Meta.AxiomGuard

/-!
# Pool classes from the side of the class

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-34.

A face class of the pocket walk lies on one side of `K.faces`
(`extremalJordanPickPool_mem_faces_iff`): a face step keeps the face, and crossing an edge off
the walk keeps the side.  Hence:

* an **outside** class avoiding the exterior and source faces is a pool class
  (`extremalJordanPickPool_of_outside`): it avoids every face of `K.faces`, so the kept cell
  `K.kept` is a witness, and every arc dart is kept;
* an **inside** class that avoids some cell of `K.faces` and meets no arc dart is a pool class
  (`extremalJordanPickPool_of_inside`): it avoids the exterior and source faces, which lie
  outside `K.faces`, and every arc dart is kept, since its reverse is outside `K.faces`.

`ExtremalJordanPickPoolRegion K r` is the disjunction of these two region conditions, and
`extremalJordanPickPool_of_region` turns it into `ExtremalJordanPickPool K r`.  The outside case
parallels the extra exterior class of `Piece10Live/ExtremalArcEndSurgery`, which is not imported.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section PickPoolSide

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A face class lies on one side of `K.faces`.** -/
theorem extremalJordanPickPool_mem_faces_iff (K : PocketFaceSet D eps X lo hi)
    {x y : X.toCombMap.Dart}
    (h : Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) x y) :
    X.toCombMap.faceOf x ∈ K.faces ↔ X.toCombMap.faceOf y ∈ K.faces := by
  induction h with
  | rel a _ hab =>
      rcases hab with rfl | ⟨hnk, rfl⟩
      · rw [X.toCombMap.faceOf_facePerm]
      · constructor
        · intro ha
          by_contra hb
          exact hnk (Or.inl ((K.boundary.cycle_mem_iff a).mpr ⟨ha, hb⟩))
        · intro hb
          by_contra ha
          refine hnk (Or.inr ((K.boundary.cycle_mem_iff (X.toCombMap.alpha a)).mpr ⟨hb, ?_⟩))
          rw [X.toCombMap.alpha_involutive a]
          exact ha
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **A dart outside the class, with its reverse outside, is kept.** -/
theorem extremalJordanPickPool_kept (K : PocketFaceSet D eps X lo hi) (r x : X.toCombMap.Dart)
    (h₁ : ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x)
    (h₂ : ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r
        (X.toCombMap.alpha x)) :
    P10ExtremalResidual.keptPred K r x = true :=
  (movePred_eq_true_iff X.toCombMap
    (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) x).mpr
    ⟨regionColour_eq_false X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) h₁,
      regionColour_eq_false X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) h₂⟩

/-- **A target dart is a walk dart.** -/
theorem extremalJordanPickPool_mem_cycle_of_target (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ K.targetArc.darts) : d ∈ K.boundary.cycle := by
  rw [K.decomposition]
  exact List.mem_append.mpr (Or.inr hd)

/-- **A dart of the reversed source arc is a walk dart.** -/
theorem extremalJordanPickPool_mem_cycle_of_invSource (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ invDarts X K.sourceArc.darts) : d ∈ K.boundary.cycle := by
  rw [K.decomposition]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
    (List.mem_append.mpr (Or.inr hd)))))

/-- **A walk dart has its face in `K.faces`.** -/
theorem extremalJordanPickPool_face_mem_of_cycle (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ K.boundary.cycle) : X.toCombMap.faceOf d ∈ K.faces :=
  ((K.boundary.cycle_mem_iff d).mp hd).1

/-- **An outside class avoiding the exterior and source faces is a pool class.** -/
theorem extremalJordanPickPool_of_outside (K : PocketFaceSet D eps X lo hi)
    {r : X.toCombMap.Dart} (hr : X.toCombMap.faceOf r ∉ K.faces)
    (hO : ∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x)
    (hS : ∀ x, X.toCombMap.faceOf x = (cell X K.source).face → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) :
    ExtremalJordanPickPool K r := by
  have hin : ∀ x, X.toCombMap.faceOf x ∈ K.faces → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x :=
    fun x hx hrx => hr ((extremalJordanPickPool_mem_faces_iff K hrx).mpr hx)
  refine ⟨⟨Or.inr hO, Or.inr hS, K.kept, K.kept_mem, fun x hx => hin x ?_⟩, ?_, ?_⟩
  · rw [hx]
    exact K.kept_mem
  · refine extremalJordan_arcEnd_of_uniform K r K.targetArc.darts (Or.inl fun x hx => ?_)
    exact extremalJordanPickPool_kept K r x
      (hin x (extremalJordanPickPool_face_mem_of_cycle K
        (extremalJordanPickPool_mem_cycle_of_target K hx)))
      (hO _ (P10Rose.FilterMove.faceOf_alpha_of_mem_targetArc K hx))
  · refine extremalJordan_arcEnd_of_uniform K r (invDarts X K.sourceArc.darts)
      (Or.inl fun x hx => ?_)
    exact extremalJordanPickPool_kept K r x
      (hin x (extremalJordanPickPool_face_mem_of_cycle K
        (extremalJordanPickPool_mem_cycle_of_invSource K hx)))
      (hS _ (P10Rose.FilterMove.faceOf_alpha_of_mem_invSourceArc K hx))

/-- **An inside class avoiding a cell of `K.faces` and every arc dart is a pool class.** -/
theorem extremalJordanPickPool_of_inside (K : PocketFaceSet D eps X lo hi)
    {r : X.toCombMap.Dart} (hr : X.toCombMap.faceOf r ∈ K.faces)
    (hkept : ∃ kept : Fin X.rCellCount, (cell X kept).face ∈ K.faces ∧
      ∀ x, X.toCombMap.faceOf x = (cell X kept).face → ¬Relation.EqvGen
        (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x)
    (harc : ∀ d ∈ K.targetArc.darts ++ invDarts X K.sourceArc.darts, ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r d) :
    ExtremalJordanPickPool K r := by
  have hout : ∀ x, X.toCombMap.faceOf x ∉ K.faces → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x :=
    fun x hx hrx => hx ((extremalJordanPickPool_mem_faces_iff K hrx).mp hr)
  refine ⟨⟨Or.inr fun x hx => hout x ?_, Or.inr fun x hx => hout x ?_, hkept⟩, ?_, ?_⟩
  · rw [hx]
    exact K.outerFace_not_mem
  · rw [hx]
    exact K.source_not_mem
  · refine extremalJordan_arcEnd_of_uniform K r K.targetArc.darts (Or.inl fun x hx => ?_)
    refine extremalJordanPickPool_kept K r x (harc x (List.mem_append_left _ hx)) (hout _ ?_)
    rw [P10Rose.FilterMove.faceOf_alpha_of_mem_targetArc K hx]
    exact K.outerFace_not_mem
  · refine extremalJordan_arcEnd_of_uniform K r (invDarts X K.sourceArc.darts)
      (Or.inl fun x hx => ?_)
    refine extremalJordanPickPool_kept K r x (harc x (List.mem_append_right _ hx)) (hout _ ?_)
    rw [P10Rose.FilterMove.faceOf_alpha_of_mem_invSourceArc K hx]
    exact K.source_not_mem

/-- **The region condition**: an outside class avoiding the exterior and source faces, or an
inside class avoiding a cell of `K.faces` and meeting no dart of either arc. -/
def ExtremalJordanPickPoolRegion (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart) :
    Prop :=
  (X.toCombMap.faceOf r ∉ K.faces ∧
    (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
    ∀ x, X.toCombMap.faceOf x = (cell X K.source).face → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∨
  (X.toCombMap.faceOf r ∈ K.faces ∧
    (∃ kept : Fin X.rCellCount, (cell X kept).face ∈ K.faces ∧
      ∀ x, X.toCombMap.faceOf x = (cell X kept).face → ¬Relation.EqvGen
        (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
    ∀ d ∈ K.targetArc.darts ++ invDarts X K.sourceArc.darts, ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r d)

/-- **A region class is a pool class.** -/
theorem extremalJordanPickPool_of_region (K : PocketFaceSet D eps X lo hi)
    {r : X.toCombMap.Dart} (h : ExtremalJordanPickPoolRegion K r) :
    ExtremalJordanPickPool K r := by
  rcases h with ⟨hr, hO, hS⟩ | ⟨hr, hkept, harc⟩
  · exact extremalJordanPickPool_of_outside K hr hO hS
  · exact extremalJordanPickPool_of_inside K hr hkept harc

end PickPoolSide

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickPool_mem_faces_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickPool_kept
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickPool_mem_cycle_of_target
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickPool_mem_cycle_of_invSource
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickPool_face_mem_of_cycle
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickPool_of_outside
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickPool_of_inside
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalJordanPickPoolRegion
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickPool_of_region
