import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcAuditStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-26: the corrected residual with local step clauses

## LOUD: lane 21a's `witnessFaces` cannot serve branch 1 of the corrected residual

This refutes the expected route for branch 1 of `PocketFourPieceArcAuditResidualStatement`
(`FourPieceArcAuditStatement.lean`), which reuses `FourPieceWitness.witnessFaces`
(`FourPieceWitnessDef.lean`).  The corrected residual itself is not refuted.

*Model M12.*  The boundary of `Π_i` is four loops at one vertex `v`:
* `λ = [y₁..x₁]` encloses a relator cell `C`;
* `μ = [g..z]` encloses an `a`-lobe `A'`;
* `λ' = [y₂..x₂]` encloses a relator cell `C'`;
* `μ'` carries both contacts, with `B_main | e | A_main` at `v`.

Take `G₁ = [λ, μ, λ']`.  The rotation at `v` is
`y₁ [C] αx₁ [Π_i] g [A'] αz [Π_i] y₂ [C'] αx₂ [Π_i] g' [B_main] e [A_main] αz' [Π_i] y₁`.
* `A'` is an `a`-face on the side of `K` and off the `Q₀`-class of `C`, so it is cut.  Then
  `witnessFaces = {C, C'}`.
* The walk is `[λ, λ']`: all `G₁`, with two non-step jumps `x₁ → y₂` and `x₂ → y₁`.  So clause 4b
  fails, and branch 2 fails too, for `witnessFaces`.
* With `faces = {C, A', C'}` the walk is `[λ, μ, λ']`, one cyclic arc.  Clause 2' exempts its `G₁`
  darts, so branch 1 holds.

*Model M6/M11.*  The same happens with a non-`G₁` dart on the walk: the jump over the `A'` sector
breaks clause 4a.  So any clause-4 statement about `witnessFaces` is false.  A witness for branch 1
must absorb the lobes behind `G`-loops.

## The remaining gap (`PocketFourPieceArcCloseStepStatement`)

It has the premise block and branch 2 of the corrected residual.  Branch 1 keeps clauses 1, 2' and
the four no-interleave clauses.  Clause 4 is replaced by local step clauses on the walk:
* **S1a.**  If some walk dart is off `G₁`, then at every position `p` where `ow[p]` and
  `ow[(p+1) % |ow|]` both lie on `G₁`, `facePerm ow[p]` is kept or `ow[p]` is pinch-free.
* **S1b.**  If every walk dart lies on `G₁`, at most one position is neither kept nor pinch-free.
* The same two clauses for `G₂/j`.

`arcAuditResidual_of_arcCloseStep` (`FourPieceArcCloseReduce.lean`) derives the corrected residual
from this statement.  All the rotation, `invDarts` and arc-extraction work is proved in
`FourPieceArcCloseStep.lean` and `FourPieceArcCloseArc.lean`.  Only pointwise clauses about single
walk positions remain, so the gap is strictly smaller in proof content.

**Truth status.**  Given `EnclosedFaceSetSucc`, S1a is implied by clause 4a (apply it to the
two-entry block of a consecutive `G₁` pair; the step puts `facePerm ow[p]` on the walk), and S1b
by clause 4b.  So the gap is true exactly when the corrected residual is.  It was checked on paper
against M2, M5, M6, M7 and M12 with lobe-absorbing witnesses.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Remaining gap of lane gl-p07-26.**  See the module docstring. -/
def PocketFourPieceArcCloseStepStatement : Prop :=
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
            ((∃ d ∈ outerWalk, d ∉ G₁.darts) →
              ∀ (p : ℕ) (hp : p < outerWalk.length), outerWalk[p] ∈ G₁.darts →
                outerWalk[(p + 1) % outerWalk.length]'(Nat.mod_lt _
                  (Nat.lt_of_le_of_lt (Nat.zero_le p) hp)) ∈ G₁.darts →
                walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[p]) ∨
                  PocketRun.PinchFreeAt X.toCombMap outerWalk[p]) ∧
            ((∀ d ∈ outerWalk, d ∈ G₁.darts) →
              ∀ (p q : ℕ) (hp : p < outerWalk.length) (hq : q < outerWalk.length),
                ¬ (walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[p]) ∨
                  PocketRun.PinchFreeAt X.toCombMap outerWalk[p]) →
                ¬ (walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[q]) ∨
                  PocketRun.PinchFreeAt X.toCombMap outerWalk[q]) → p = q) ∧
            ((∃ d ∈ outerWalk, d ∉ G₂.darts) →
              ∀ (p : ℕ) (hp : p < outerWalk.length), outerWalk[p] ∈ G₂.darts →
                outerWalk[(p + 1) % outerWalk.length]'(Nat.mod_lt _
                  (Nat.lt_of_le_of_lt (Nat.zero_le p) hp)) ∈ G₂.darts →
                walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[p]) ∨
                  PocketRun.PinchFreeAt X.toCombMap outerWalk[p]) ∧
            ((∀ d ∈ outerWalk, d ∈ G₂.darts) →
              ∀ (p q : ℕ) (hp : p < outerWalk.length) (hq : q < outerWalk.length),
                ¬ (walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[p]) ∨
                  PocketRun.PinchFreeAt X.toCombMap outerWalk[p]) →
                ¬ (walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[q]) ∨
                  PocketRun.PinchFreeAt X.toCombMap outerWalk[q]) → p = q)) ∨
        (∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart) (n : ℕ),
          EnclosedFaceSetSucc X faces outerWalk ∧ C.face ∈ faces ∧
            ((∃ A : CyclicArc (cellDarts X i),
                invDarts X (outerWalk.rotate n) = invDarts X A.darts) ∨
              (∃ A : CyclicArc (cellDarts X j),
                invDarts X (outerWalk.rotate n) = invDarts X A.darts)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceArcCloseStepStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
