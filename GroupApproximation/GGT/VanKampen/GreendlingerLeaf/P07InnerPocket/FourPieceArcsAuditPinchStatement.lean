import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessArcsStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-29: the arc audit under a pinch bound

## LOUD: `FourPieceWitness.ArcsAuditStatement` (`FourPieceWitnessArcsStatement.lean`) is FALSE

This is a paper model; the statement has not been formally refuted.

*Model M11 (a lobe inside a third `G₁`-loop).*
* **The cell.**  `Π_i` is pinched at a vertex `v` that its boundary visits four times.  The
  boundary is `μh ⋯ μt` (the outer loop, which carries `a.arc` and `b.arc`), then the inner
  loops `λ`, `ν`, `λ'`, in `facePerm` order.  `G₁ = μt' λ ν λ' μh'`, where `μt'` and `μh'` are
  the parts of `μ` next to `v`.  The four sectors at `v` are the `λ`-disc, the `ν`-disc, the
  `λ'`-disc and the outer region `O`.
* **The regions.**  The `λ`-disc is one relator cell `C`, and the `λ'`-disc holds a relator cell
  `C'` at `v`.  The candidate `a` is pinched at `v` (allowed, see `pasting` in
  `ContiguityGeometry`): its main strip lies in `O`, and a lobe `A'` lies in the `ν`-disc and
  touches `v`.  `b` is an ordinary strip.
* **The witness.**  Every face of the `ν`-disc is edge-joined, off `block`, to `A'`, so it is cut.
  In `O` near `v`, the piece of the boundary of `a` from `v` to the junction `v₀` of `a.arc` and
  `G₁`, together with `μt'`, closes off a cut region.  This is the M6 argument of lane gl-p07-25,
  which acts on `O`, not on the `λ`- or `λ'`-disc.  `C` and `C'` are open and share `v`, so they
  `Touch`.  So `C'` lies in `F = witnessFaces a b K C.face`.
* **The walk.**  At `v`, `turn_next` sends `λ_end` past the `ν`-sector (nothing there is kept) to
  `λ'_1`, but `facePerm λ_end = ν_1`.
* **Failure.**  If `F` also reaches the pocket in `O`, a rotation-prefix block `[…, λ_end, λ'_1,
  …] ⊆ G₁`, whose complement leaves `G₁`, is not a cell arc, so clause 4a fails.  If
  `F = {C} ∪ λ'`-disc, the walk is `λ λ'`, with two junctions `λ_end → λ'_1` and
  `λ'_end → λ_1`.  No rotation is a cell arc, so clause 4b fails.

*Model M9/M10* is the same picture with `A'` replaced by an M8 empty-arc island `a.1` inside the
`ν`-disc (`FourPieceWitnessPlanarAudit.lean`).  A `b`-lobe next to the `a`-lobe in the same
`ν`-disc changes nothing.  Every `ν`-sector face is still cut, and `λ`, `λ'` are untouched.

**Where the lane-21c mechanism breaks.**  A jump `p → q` inside `G₁` does force a pinch at `v`.
But the loop that the jump skips (here `ν`) need not contain a walk dart off `G₁`.  It may contain
only cut faces, while the `F`-corners on both sides still `Touch` at `v`.

## The corrected statement (`FourPieceWitness.ArcsAuditPinchStatement`)

It keeps the premise block of `ArcsAuditStatement` and adds a hypothesis to each clause.
* **4a** (for `G₁` and `Π_i`) assumes that every dart `d` of `G₁` is pinch-free
  (`PocketRun.PinchFreeAt`, lane gl-p07-09): the only dart of `Π_i` starting at the end vertex of
  `d` is `facePerm d`.
* **4b** assumes that at most one dart of `G₁` is not pinch-free.
* The same two clauses hold for `G₂` and `Π_j`.

It is strictly weaker than `ArcsAuditStatement`, since each clause only gains a hypothesis.  It is
**proved** in `FourPieceArcsAuditPinchProof.lean` from lane gl-p07-26 (`ArcClose.arc_of_block` and
`ArcClose.arc_of_all`).  It excludes M9, M10 and M11: `λ_end`, `ν_end` and `λ'_end` all end at
`v`, and Π_i has other darts starting there.  It keeps M2 of lane gl-p07-21c, where the only
pinched dart of `G₁` is the last dart `x` of `λ`.

**Remaining gap.**  `FourPieceWitness.arcAuditResidual_of_planar_noninterleave_arcsAudit`
consumes the uncorrected `ArcsAuditStatement`.  The consumer needs either pinch-free cells, or a
separate treatment of a loop of `Π_i` at `v` that holds only cut faces (M11).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Clauses 4a and 4b for the cut-down witness, under a pinch bound on the cell arcs.**  See the
module docstring. -/
def ArcsAuditPinchStatement : Prop :=
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
      ∀ outerWalk : List X.toCombMap.Dart,
        EnclosedFaceSetSucc X (witnessFaces a b K C.face) outerWalk →
        (∀ d ∈ outerWalk,
          X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K C.face) →
        ((∀ d ∈ G₁.darts, PocketRun.PinchFreeAt X.toCombMap d) →
          ∀ (m : ℕ) (U V : List X.toCombMap.Dart),
          (invDarts X outerWalk).rotate m = U ++ V →
          (∀ e ∈ U, e ∈ invDarts X G₁.darts) →
          (∃ e ∈ V, e ∉ invDarts X G₁.darts) →
          ∃ A : CyclicArc (cellDarts X i), U = invDarts X A.darts) ∧
        ((∀ d ∈ G₁.darts, ∀ d' ∈ G₁.darts, ¬ PocketRun.PinchFreeAt X.toCombMap d →
            ¬ PocketRun.PinchFreeAt X.toCombMap d' → d = d') →
          (∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₁.darts) →
          ∃ (n : ℕ) (A : CyclicArc (cellDarts X i)),
            invDarts X (outerWalk.rotate n) = invDarts X A.darts) ∧
        ((∀ d ∈ G₂.darts, PocketRun.PinchFreeAt X.toCombMap d) →
          ∀ (m : ℕ) (U V : List X.toCombMap.Dart),
          (invDarts X outerWalk).rotate m = U ++ V →
          (∀ e ∈ U, e ∈ invDarts X G₂.darts) →
          (∃ e ∈ V, e ∉ invDarts X G₂.darts) →
          ∃ A : CyclicArc (cellDarts X j), U = invDarts X A.darts) ∧
        ((∀ d ∈ G₂.darts, ∀ d' ∈ G₂.darts, ¬ PocketRun.PinchFreeAt X.toCombMap d →
            ¬ PocketRun.PinchFreeAt X.toCombMap d' → d = d') →
          (∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₂.darts) →
          ∃ (n : ℕ) (A : CyclicArc (cellDarts X j)),
            invDarts X (outerWalk.rotate n) = invDarts X A.darts)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.ArcsAuditPinchStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
