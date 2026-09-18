import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalBlockNoWrap
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalRegionLists
import GroupApproximation.Meta.AxiomGuard

/-!
# The extremal region: choice clauses

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-14.

The clauses of `P10ExtremalWrap.ExtremalBlockNoWrapClauses` phrased directly in terms of the
region `r` (a class of `FaceClassStep` for the walk `K.boundary.cycle`), without flip face sets:

* `RegionChoice K r`: some relator cell `kept` has its face in `K.faces`, and the class of `r`
  meets no dart of the exterior face, of the source face, or of the kept face.
* `StretchesClosed K r`: between two consecutive darts of `K.boundary.cycle` kept by the move at
  `r` (`P10ExtremalResidual.keptPred`), the removed stretch `B` is a closed walk: it starts at the
  vertex where it ends.
* `flipClauses_of_regionChoice`: `RegionChoice` gives the three flip clauses (exterior face
  avoided, source face not flipped, kept face flipped).
* `isChain_filter_keptPred_of_stretchesClosed`: in a pocket in walk order, closed stretches make
  the kept darts a walk (`ExtremalRegionLists.isChain_filter_of_closedStretches`).

Truth of `RegionChoice`: in the finite plane Eulerian model of the pocket boundary (lane
gl-p10-12b/13/14 search, `subarc_search`), a valid region avoids the exterior region, the source
region and the region of some kept cell; this is exactly `RegionChoice`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section Choice

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The region choice**: a kept relator cell inside the pocket, and the class of `r` avoiding
the exterior face, the source face and the kept face. -/
def RegionChoice (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart) : Prop :=
  ∃ kept : Fin X.rCellCount, (cell X kept).face ∈ K.faces ∧
    ∀ x, (X.toCombMap.faceOf x = X.outerFace ∨ X.toCombMap.faceOf x = (cell X K.source).face ∨
      X.toCombMap.faceOf x = (cell X kept).face) →
      ¬Relation.EqvGen
        (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x

/-- **Closed removed stretches**: every stretch of removed darts between two consecutive kept
darts of `K.boundary.cycle` starts where it ends. -/
def StretchesClosed (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart) : Prop :=
  ∀ (A : List X.toCombMap.Dart) (d : X.toCombMap.Dart) (B : List X.toCombMap.Dart)
    (e : X.toCombMap.Dart) (C : List X.toCombMap.Dart),
    K.boundary.cycle = A ++ d :: (B ++ e :: C) → P10ExtremalResidual.keptPred K r d = true →
      P10ExtremalResidual.keptPred K r e = true →
      (∀ x ∈ B, P10ExtremalResidual.keptPred K r x = false) →
      ∀ b₀ ∈ B.head?, ∀ b₁ ∈ B.getLast?,
        X.toCombMap.vertexOf b₀ = X.toCombMap.vertexOf (X.toCombMap.alpha b₁)

/-- **The flip clauses from the region choice.** -/
theorem flipClauses_of_avoid (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart)
    (kept : Fin X.rCellCount) (hkf : (cell X kept).face ∈ K.faces)
    (havoid : ∀ x, (X.toCombMap.faceOf x = X.outerFace ∨
      X.toCombMap.faceOf x = (cell X K.source).face ∨
      X.toCombMap.faceOf x = (cell X kept).face) →
      ¬Relation.EqvGen
        (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) :
    (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
    (cell X K.source).face ∉ flipFaces X.toCombMap K.faces
      (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) ∧
    (cell X kept).face ∈ flipFaces X.toCombMap K.faces
      (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) := by
  have hz := regionColour_step X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r
  refine ⟨fun x hx => havoid x (Or.inl hx), ?_, ?_⟩
  · exact not_mem_flipFaces hz K.source_not_mem fun x hx =>
      regionColour_eq_false X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)
        (havoid x (Or.inr (Or.inl hx)))
  · exact mem_flipFaces hz hkf fun x hx =>
      regionColour_eq_false X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)
        (havoid x (Or.inr (Or.inr hx)))

/-- **Closed stretches make the kept darts a walk** in a pocket in walk order. -/
theorem isChain_filter_keptPred_of_stretchesClosed (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) (r : X.toCombMap.Dart) (hstr : StretchesClosed K r) :
    (K.boundary.cycle.filter (P10ExtremalResidual.keptPred K r)).IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e := by
  have hc : K.boundary.cycle.IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e := And.left hK
  exact isChain_filter_of_closedStretches (fun d => X.toCombMap.vertexOf (X.toCombMap.alpha d))
    X.toCombMap.vertexOf (P10ExtremalResidual.keptPred K r) hc hstr

end Choice

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.RegionChoice
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.StretchesClosed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.flipClauses_of_avoid
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.isChain_filter_keptPred_of_stretchesClosed
