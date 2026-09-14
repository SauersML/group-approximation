import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellTouchOnly
import GroupApproximation.GGT.VanKampen.ClosedWalkPinchSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# Splitting a vertex touch of a pocket walk: the corner statement

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, across one relator cell: the touch-only X-pocket
(`OsinLemma94CaseOneTouchOnlyStatement`).  The pocket walk `invDarts X ++ invDarts B` passes a
touch vertex `v` twice, as two passages `in₁ → out₁` and `in₂ → out₂`.  Splitting `v` at
`alpha in₁` and `alpha in₂` (`PinchSplit.Input.diagram`) puts the two passages on different
vertices and keeps every dart, label, relator word and the exterior word.  The split merges the two
corner faces `faceOf in₁` and `faceOf in₂`, which lie on the side of the walk, and it needs them to
be distinct G-faces.

`OsinPocketTouchCornerStatement` is that input.  It gives an O-equivalent copy with letter labels
and a dart map `e` that commutes with edge reversal, keeps labels, reflects and preserves vertices,
and keeps vertex rotation away from the four corners of `in₁` and `in₂` (the corners after
`alpha in₁`, `alpha in₂` and before `in₁`, `in₂`).  In the copy, `e in₁` and `e in₂` lie on distinct
G-faces off the exterior, the exterior and the carrier of the relator cell stay off the side of the
transported walk, and the carrier of the cell is transported by `e`.  An edge doubling along `in₁`
inside `faceOf in₁` and along `in₂` inside `faceOf in₂` has these properties.

Lanes: the producer is `ms-compress-2` (`Estimating/OsinPocketTouchCornerThickening.lean`); the
split transport, the induction on the number of touch vertices and the touch-only leaf are
`ms-inverses-4`'s.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.4, Case 1).  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

/-- **The corners of a vertex touch are distinct G-faces, up to O-equivalence.**  Let `X` carry
letter labels, let `walk` be a closed dart walk with the exterior and the carrier of a relator cell
`i` off its side, and let `in₁ ≠ in₂` be darts of the walk that end at one vertex and are not
loops.  Then there are an O-equivalent copy `X'` with letter labels and a dart map `e` such that:

* `e` is injective, commutes with edge reversal, keeps labels, and reflects and preserves vertices;
* `e` keeps vertex rotation at every dart `d` other than `alpha in₁`, `alpha in₂` whose successor
  is not `in₁`, `in₂`;
* `e in₁` and `e in₂` lie on distinct faces of `X'`, neither the exterior nor a relator face;
* the exterior and the carrier of a relator cell `i'` are off the side of `walk.map e`, and the
  carrier of `i'` is the carrier of `i` mapped by `e`. -/
def OsinPocketTouchCornerStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (X : DiscDiagram.{u, w, v} W),
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ (walk : List X.toCombMap.Dart), IsClosedDartWalk X.toCombMap walk →
    ∀ in₁ ∈ walk, ∀ in₂ ∈ walk, in₁ ≠ in₂ →
      X.toCombMap.vertexOf (X.toCombMap.alpha in₁) =
        X.toCombMap.vertexOf (X.toCombMap.alpha in₂) →
      X.toCombMap.vertexOf in₁ ≠ X.toCombMap.vertexOf (X.toCombMap.alpha in₁) →
      X.toCombMap.vertexOf in₂ ≠ X.toCombMap.vertexOf (X.toCombMap.alpha in₂) →
      X.outerFace ∉ sideFaces X.toCombMap walk →
      ∀ (i : Fin X.rCellCount), (cell X i).face ∉ sideFaces X.toCombMap walk →
        ∃ (X' : DiscDiagram.{u, w, v} W) (e : X.toCombMap.Dart → X'.toCombMap.Dart)
          (i' : Fin X'.rCellCount),
          Nonempty (OEquivalentDiscDiagram X X') ∧
          (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
          Function.Injective e ∧
          (∀ d, X'.toCombMap.alpha (e d) = e (X.toCombMap.alpha d)) ∧
          (∀ d, X'.label (e d) = X.label d) ∧
          (∀ d d', X'.toCombMap.vertexOf (e d) = X'.toCombMap.vertexOf (e d') ↔
            X.toCombMap.vertexOf d = X.toCombMap.vertexOf d') ∧
          (∀ d, d ≠ X.toCombMap.alpha in₁ → d ≠ X.toCombMap.alpha in₂ →
            X.toCombMap.sigma d ≠ in₁ → X.toCombMap.sigma d ≠ in₂ →
              X'.toCombMap.sigma (e d) = e (X.toCombMap.sigma d)) ∧
          X'.toCombMap.faceOf (e in₁) ≠ X'.toCombMap.faceOf (e in₂) ∧
          X'.toCombMap.faceOf (e in₁) ≠ X'.outerFace ∧
          X'.toCombMap.faceOf (e in₂) ≠ X'.outerFace ∧
          (∀ C ∈ X'.relatorCells, C.face ≠ X'.toCombMap.faceOf (e in₁)) ∧
          (∀ C ∈ X'.relatorCells, C.face ≠ X'.toCombMap.faceOf (e in₂)) ∧
          X'.outerFace ∉ sideFaces X'.toCombMap (walk.map e) ∧
          (cell X' i').face ∉ sideFaces X'.toCombMap (walk.map e) ∧
          cellDarts X' i' = (cellDarts X i).map e

end GroupApproximation.GGT.VanKampen
