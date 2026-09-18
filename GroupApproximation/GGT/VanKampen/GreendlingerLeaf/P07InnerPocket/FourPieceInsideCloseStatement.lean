import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcAuditStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-45: the inside clause needs side inclusion only for lake walks

The target is `PocketFourPieceInsideStatement` (`FourPieceOffSplit.lean`).  It is
`SideBoundFourPieceInputStatement` with one more clause: if both arcs are empty, then
`faces ⊆ sideFaces K.walk`.

## What the inside clause really consumes

The route is `pocketFourPieceInside_of_arcAuditResidual` (`FourPieceArcAuditInside.lean`).  It gets
the inside clause from clause 3 of branch 1 of `PocketFourPieceArcAuditResidualStatement`, which is
`faces ⊆ sideFaces K.walk` for *every* branch-1 witness.  The inside clause only needs it when
`A₁` and `A₂` are both empty.  In the four-piece reading `R₁ ++ U₁ ++ R₂ ++ U₂`, the runs `U₁` and
`U₂` are then empty, so the cyclic word is `R₁ ++ R₂`.
* The four-piece order (`FourPiece.exists_fourPiece`) is run with the labels
  `Pa' e := α e ∈ a.sideFrom j ∧ e ∉ Ḡ₁ ∧ e ∉ Ḡ₂` and `Pb' e := α e ∈ b.sideFrom i ∧ e ∉ Ḡ₁ ∧ e ∉ Ḡ₂`.
  Here `Ḡ` is short for `invDarts X G.darts`.
* The two class hypotheses that mention `Pb` are pointwise equivalent with `Pb'`.  `Pa` occurs in
  none of them.
* So every entry of `R₁ ++ R₂` avoids `Ḡ₁` and `Ḡ₂`.  With both arcs empty, **the outside walk reads
  no gap dart**.

## The residual (`FourPieceInsideCloseResidualStatement`)

It is `PocketFourPieceArcAuditResidualStatement` with one change: clause 3 of branch 1 becomes
`(∀ e ∈ invDarts X outerWalk, e ∉ Ḡ₁ ∧ e ∉ Ḡ₂) → faces ⊆ sideFaces K.walk`.  Side inclusion is only
asked for **lake walks**, the witnesses whose outside walk reads no dart of either gap.

* `fourPieceInsideClose_residual_of_arcAuditResidual`: the arc-audit residual implies it, since the
  clause only gains a hypothesis.  So every existing route into the arc-audit residual feeds it
  (for example `SoundRoute.PinchCaseStatement`, `FourPieceArcCloseReduce.lean`,
  `NoPlanarDegenPinchProof.lean`).
* `fourPieceInsideClose_of_residual` (`FourPieceInsideCloseProof.lean`): it gives
  `PocketFourPieceInsideStatement`.

## LOUD: strength

* The new statement is **weaker or equal** as a `Prop`: it is proved from the arc-audit residual.
* It is **strictly smaller in proof content**.  A prover of branch 1 no longer has to keep the
  witness on the side of `K` when its outside walk reads a gap dart.  In the wedge model below,
  `{C, Π_j}` passes the new clause 3 (its walk reads `Ḡ₁`).  It never passes the old one, since
  `Π_j ∉ sideFaces K`.
* **Strictness as a `Prop` cannot be shown**: both statements are believed true, and true
  statements are equivalent as `Prop`s.  Neither is known false.  So this is a reduction of proof
  content, not a proof of anything false or equivalent in form.

## Truth check

* **Wedge model** (lane gl-p07-18, `FourPieceOffSplit.lean`).  `K = s₁ Ā₁ s₂ Ā₂`, with `Π_i`, `Π_j`
  hanging off the contour at one vertex each.
  - The bad lake fill `{C, Π_i, Π_j}` reads only the far sides of `b` and `a`: a lake walk.  The new
    clause still demands `faces ⊆ sideFaces K`, and that fails, so this fill is still excluded.
    That is what the off-cell half (`pocketFourPieceOffCell`) needs.
  - `{C}` is a witness exactly as for the arc-audit residual.
  - `{C, Π_j}` reads the loop of `Π_i`, which is all `Ḡ₁`.  The new clause 3 is vacuous for it.
* **M2, M7, M9, M11** (lanes 21c, 29, 31).  The arc-audit witnesses are kept, and the clause is only
  weakened.
* **Consistency with `Inside`.**  A lake walk has both arcs empty in every four-piece reading.  So
  the new clause is exactly the part of clause 3 that the inside clause of the target needs.

Truth status: at least as plausible as the arc-audit residual (UNKNOWN / plausibly true, lanes
21c, 28, 31).  **Riskiest point:** unchanged from the arc-audit residual.  Clause 4a at pinch
pathologies, and the four noninterleaving facts for the chosen witness.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Residual of lane gl-p07-45.**  This is `PocketFourPieceArcAuditResidualStatement` with clause 3
of branch 1 (`faces ⊆ sideFaces K.walk`) asked only for witnesses whose outside walk reads no
dart of `invDarts G₁` or `invDarts G₂`.  See the module docstring. -/
def FourPieceInsideCloseResidualStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j → Disjoint a.1 b.1 →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
    ∀ G₁ : CyclicArc (cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i →
    ∀ G₂ : CyclicArc (cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j →
    ∀ hw : IsNoncrossingClosedWalk X.toCombMap K.walk,
      X.outerFace ∉ sideFaces X.toCombMap K.walk →
      (reclosedMap X.toCombMap (sideFaces X.toCombMap K.walk)
          (hw.innerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      (reclosedMap X.toCombMap (sideOutside X.toCombMap K.walk)
          (hw.outerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      ∀ C ∈ X.relatorCells, C.face ∈ sideFaces X.toCombMap K.walk → C.face ∉ a.1 → C.face ∉ b.1 →
        (∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
          EnclosedFaceSetSucc X faces outerWalk ∧ C.face ∈ faces ∧
            ((∀ e ∈ invDarts X outerWalk,
                e ∉ invDarts X G₁.darts ∧ e ∉ invDarts X G₂.darts) →
              faces ⊆ sideFaces X.toCombMap K.walk) ∧
            (∀ d ∈ outerWalk,
              X.toCombMap.alpha d ∈ invDarts X G₁.darts ∨
              X.toCombMap.alpha d ∈ invDarts X G₂.darts ∨
              (X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ sideFaces X.toCombMap K.walk ∧
                X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ a.1 ∧
                X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ b.1 ∧
                (walkKeep X.toCombMap K.walk (X.toCombMap.alpha d) ∨
                  walkKeep X.toCombMap a.2.boundary.cycle (X.toCombMap.alpha d) ∨
                  walkKeep X.toCombMap b.2.boundary.cycle (X.toCombMap.alpha d)))) ∧
            FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts)
              (invDarts X outerWalk) ∧
            FourPiece.CyclicNoInterleave
              (fun e => e ∉ invDarts X G₁.darts ∧ e ∈ invDarts X G₂.darts)
              (invDarts X outerWalk) ∧
            FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts ∨
              (e ∉ invDarts X G₂.darts ∧ X.toCombMap.alpha e ∈ b.sideFrom i))
              (invDarts X outerWalk) ∧
            FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts ∨
              (e ∉ invDarts X G₂.darts ∧ X.toCombMap.alpha e ∉ b.sideFrom i))
              (invDarts X outerWalk) ∧
            (∀ (m : ℕ) (U V : List X.toCombMap.Dart),
              (invDarts X outerWalk).rotate m = U ++ V →
              (∀ e ∈ U, e ∈ invDarts X G₁.darts) →
              (∃ e ∈ V, e ∉ invDarts X G₁.darts) →
              ∃ A : CyclicArc (cellDarts X i), U = invDarts X A.darts) ∧
            ((∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₁.darts) →
              ∃ (n : ℕ) (A : CyclicArc (cellDarts X i)),
                invDarts X (outerWalk.rotate n) = invDarts X A.darts) ∧
            (∀ (m : ℕ) (U V : List X.toCombMap.Dart),
              (invDarts X outerWalk).rotate m = U ++ V →
              (∀ e ∈ U, e ∈ invDarts X G₂.darts) →
              (∃ e ∈ V, e ∉ invDarts X G₂.darts) →
              ∃ A : CyclicArc (cellDarts X j), U = invDarts X A.darts) ∧
            ((∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₂.darts) →
              ∃ (n : ℕ) (A : CyclicArc (cellDarts X j)),
                invDarts X (outerWalk.rotate n) = invDarts X A.darts)) ∨
        (∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart) (n : ℕ),
          EnclosedFaceSetSucc X faces outerWalk ∧ C.face ∈ faces ∧
            ((∃ A : CyclicArc (cellDarts X i),
                invDarts X (outerWalk.rotate n) = invDarts X A.darts) ∨
              (∃ A : CyclicArc (cellDarts X j),
                invDarts X (outerWalk.rotate n) = invDarts X A.darts)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceInsideCloseResidualStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
