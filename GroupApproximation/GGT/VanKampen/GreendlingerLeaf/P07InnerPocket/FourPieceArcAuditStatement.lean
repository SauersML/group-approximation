import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceOffSplit
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceListOrder
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-21c: audit of clause 4 of the input-proof residual

## LOUD: clause 4 of `PocketFourPieceInputProofResidualStatement` is FALSE

Clause 4 asks that *every* rotation-prefix `U` of `invDarts outerWalk` with all entries in
`invDarts G₁` be `invDarts` of a `CyclicArc (cellDarts X i)`.  This includes the whole list.

*Model M2 (crescent).*  The boundary of `Π_i` is an outer loop `μ` together with an inner loop
`λ = G₁`, and the two touch at one vertex `v`.  `λ` encloses a single relator cell `C`.  At `v` the
rotation is `λ₁ [C] αx [Π_i] μ₁ [B] e [A] αd₁ [Π_i] λ₁`.  Here `x` is the last dart of `λ`, `A` is
an `a`-face and `B` is a `b`-face, and they share the edge `e`.
* Clause 2 forbids `A` and `B` in `faces`, so `μ₁`, `e` and `αd₁` are not kept.
* So every witness walks along `λ` with the transition `x → λ₁`.
* The block `U = [αλ₁, αx]` (a rotation-prefix) is all in `G₁`.  But `[x, λ₁]` is not an arc,
  because `facePerm x = μ₁ ≠ λ₁`.

So the original residual is false.  `PocketFourPieceInsideStatement` still holds in M2: take
`walk = λ` read as one arc, with `R₁ = R₂ = []` and `A₂` empty.

*The mechanism.*  A non-`facePerm` `G₁ → G₁` transition `p → q` forces `facePerm p` to be not kept.
So `Π_i` is pinched at the vertex, and the walk stays in the region bounded by the `Π_i` boundary
from `q` to `p`.  A prefix block whose complement still holds a non-`G₁` entry cannot run through
such a transition: it would have to leave that region.  That gives clause 4a.  When the walk is all
`G₁`, it is one cyclic arc: clause 4b.

*Model M6.*  An `a`-lobe `A'` is attached at `v` behind a `G₁`-loop edge.  Clause 2 forbids
`A' ∈ faces`, which forces a non-arc block again.  Fix (clause 2'): a walk dart `d` with
`α d ∈ invDarts G₁` or `α d ∈ invDarts G₂` is exempt from the per-dart clause, so `A'` may be
enclosed.

*Model M7.*  The whole `a/Π_j/b` blob passes through the pinch `v`.  The pocket piece has two
boundary cycles touching at `v`, so no clause-2 witness exists.  `Inside` survives with
`faces = R` (bounded by one cell arc of `i`).  Fix (branch 2): a witness whose rotated inverse walk
is a single cell arc of `i` or of `j`.

## The corrected residual (`PocketFourPieceArcAuditResidualStatement`)

It has the same premise block.  Its conclusion is one of two branches.

**Branch 1.**  The original clauses, with these changes:
* **clause 2'**, the exemption above;
* **clause 4a**, where the block `U` is only required to be an arc when its complement `V` holds
  an entry outside `invDarts G₁`;
* **clause 4b**, where an all-`G₁` walk is, after a rotation, one cell arc;
* the same two changes for `G₂/j`.

**Branch 2.**  An enclosed face set `faces ∋ C` whose rotated inverse walk is one cell arc.

Each change weakens its clause, so the corrected residual follows from the original one
(`pocketFourPieceArcAuditResidual_of_inputProofResidual`, `FourPieceArcAuditWeaken.lean`).  The
original is false, so the corrected residual is strictly weaker.  It still gives
`PocketFourPieceInsideStatement` (`pocketFourPieceInside_of_arcAuditResidual`,
`FourPieceArcAuditProof.lean`).

**Truth status.**  The corrected residual was checked on paper against M2, M5 (a `b`-chord inside
the pinch region; take a smaller witness), M6 and M7.  No model refutes `Inside`.
**Riskiest point:** clause 4a for other pinch pathologies, and clause 3 for the corrected witness.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Corrected residual of lane gl-p07-20b (lane gl-p07-21c).**  See the module docstring. -/
def PocketFourPieceArcAuditResidualStatement : Prop :=
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
            faces ⊆ sideFaces X.toCombMap K.walk ∧
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

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceArcAuditResidualStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
