import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalRegion
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalClassLists
import GroupApproximation.Meta.AxiomGuard

/-!
# Extremal class: the combinatorial property and the chain consequence

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-15.

The combinatorial property of an extremal face class `r` of `walkKeep K.boundary.cycle`:

* `ExtremalClassChoice K r`: either some target dart is kept or the class avoids the exterior
  face; either some source dart is kept or the class avoids the source face; and some relator
  cell `kept` with face in `K.faces` has its face avoided by the class.
* `ExtremalClassStretches K r`: for two consecutive kept darts `d`, `e` of `K.boundary.cycle`
  separated by a NONEMPTY run of removed darts, the ends are linked
  (`vertexOf (alpha d) = vertexOf e`), and `d`, `e` do not both lie on the target arc, nor both
  on the reversed source arc.

The chain consequence, proved here:

* `sourceAvoid_of_keptSource`: a kept source dart keeps the class off the source face.
* `regionChoice_of_classChoice`: `ExtremalClassChoice` gives `RegionChoice`.
* `stretchesClosed_of_classStretches`: in walk order, linked ends make each removed stretch a
  closed walk (`closed_stretch_of_rel`), so `ExtremalClassStretches` gives `StretchesClosed`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section ClassChoice

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The extremal class choice**: exterior and source faces avoided unless a dart of the
corresponding arc is kept, and some kept cell of `K.faces` avoided. -/
def ExtremalClassChoice (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart) : Prop :=
  ((∃ e ∈ K.targetArc.darts, P10ExtremalResidual.keptPred K r e = true) ∨
    ∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
  ((∃ e ∈ K.sourceArc.darts, P10ExtremalResidual.keptPred K r e = true) ∨
    ∀ x, X.toCombMap.faceOf x = (cell X K.source).face → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
  ∃ kept : Fin X.rCellCount, (cell X kept).face ∈ K.faces ∧
    ∀ x, X.toCombMap.faceOf x = (cell X kept).face → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x

/-- **The extremal class stretches**: consecutive kept darts separated by a nonempty removed run
have linked ends and do not both lie on one arc. -/
def ExtremalClassStretches (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart) : Prop :=
  ∀ (A : List X.toCombMap.Dart) (d : X.toCombMap.Dart) (B : List X.toCombMap.Dart)
    (e : X.toCombMap.Dart) (C : List X.toCombMap.Dart),
    K.boundary.cycle = A ++ d :: (B ++ e :: C) → P10ExtremalResidual.keptPred K r d = true →
      P10ExtremalResidual.keptPred K r e = true →
      (∀ x ∈ B, P10ExtremalResidual.keptPred K r x = false) → B ≠ [] →
        X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e ∧
        ¬(d ∈ K.targetArc.darts ∧ e ∈ K.targetArc.darts) ∧
        ¬(d ∈ invDarts X K.sourceArc.darts ∧ e ∈ invDarts X K.sourceArc.darts)

/-- **A kept source dart keeps the class off the source face.** -/
theorem sourceAvoid_of_keptSource (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart)
    {e : X.toCombMap.Dart} (he : e ∈ K.sourceArc.darts)
    (hk : P10ExtremalResidual.keptPred K r e = true) :
    ∀ x, X.toCombMap.faceOf x = (cell X K.source).face → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x := by
  intro x hx hrx
  have hfe : X.toCombMap.faceOf e = (cell X K.source).face :=
    ((X.faceBoundary (cell X K.source).face).mem_iff e).mp
      (K.sourceArc.mem_cycle_of_mem_darts he)
  have hsame := (X.toCombMap.faceOf_eq_iff e x).mp (hfe.trans hx.symm)
  have hre : Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r e :=
    Relation.EqvGen.trans _ _ _ hrx (Relation.EqvGen.symm _ _
      (eqvGen_faceClass_of_sameCycle X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) hsame))
  have h1 := ((movePred_eq_true_iff X.toCombMap
    (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) e).mp hk).1
  rw [(regionColour_eq_true_iff X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r
    e).mpr hre] at h1
  exact absurd h1 (by decide)

/-- **The region choice from the extremal class choice.** -/
theorem regionChoice_of_classChoice (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart)
    (h : ExtremalClassChoice K r) : RegionChoice K r := by
  obtain ⟨hout, hsrc, kept, hkf, hkav⟩ := h
  refine ⟨kept, hkf, ?_⟩
  rintro x (hx | hx | hx)
  · rcases hout with ⟨e, he, hk⟩ | hout
    · exact P10ExtremalBlock.outerAvoid_of_keptTarget K r he hk x hx
    · exact hout x hx
  · rcases hsrc with ⟨e, he, hk⟩ | hsrc
    · exact sourceAvoid_of_keptSource K r he hk x hx
    · exact hsrc x hx
  · exact hkav x hx

/-- **Closed stretches from the extremal class stretches**, in walk order. -/
theorem stretchesClosed_of_classStretches (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (r : X.toCombMap.Dart) (h : ExtremalClassStretches K r) : StretchesClosed K r := by
  intro A d B e C hc hd he hB b₀ hb₀
  have hne : B ≠ [] := by
    rintro rfl
    simp at hb₀
  have hchain : K.boundary.cycle.IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e := And.left hK
  rw [hc] at hchain
  exact closed_stretch_of_rel (fun d => X.toCombMap.vertexOf (X.toCombMap.alpha d))
    X.toCombMap.vertexOf hchain.right_of_append (h A d B e C hc hd he hB hne).1 b₀ hb₀

end ClassChoice

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalClassChoice
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalClassStretches
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.sourceAvoid_of_keptSource
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.regionChoice_of_classChoice
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.stretchesClosed_of_classStretches
