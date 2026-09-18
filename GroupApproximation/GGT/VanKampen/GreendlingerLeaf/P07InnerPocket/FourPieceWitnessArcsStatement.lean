import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessRead
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-25: the arc clauses for the witness, corrected

## LOUD: `PocketFourPieceWitnessArcsStatement` (`FourPieceWitnessRead.lean`) is FALSE

The counterexample is model M2 from lane gl-p07-21c (`FourPieceArcAuditStatement.lean`).
* **The picture.**  The boundary of `Π_i` is an outer loop `μ` plus an inner loop `λ = G₁`, and
  the two meet at one vertex `v`.  `λ` encloses one relator cell `C`.  At `v` the rotation is
  `λ₁ [C] αx [Π_i] μ₁ [B] e [A] αd₁ [Π_i] λ₁`, with `A ∈ a` and `B ∈ b`.
* **The witness.**  `A` and `B` are cut.  Every edge of `λ` is a walk edge with `Π_i` in
  `sideOutside K.walk`.  So `F = witnessFaces a b K C.face = {C}`, and its outside walk is `λ` in
  `facePerm` order.
* **Where it fails.**  The rotation-prefix `U = [αλ₁, αx]` lies in `invDarts G₁`.  But
  `facePerm x = μ₁ ≠ λ₁`, so `U` is not `invDarts` of any cell arc.

So `inputProofResidual_of_witness_noninterleave_arcs` (`FourPieceWitnessProof.lean`) has a false
conclusion.  Of its three hypotheses, the false one is the arc statement.

## The corrected statement (`FourPieceWitness.ArcsAuditStatement`)

It has the same premise block and the same walk hypotheses.  Its conclusion is clauses 4a and 4b of
`PocketFourPieceArcAuditResidualStatement`:
* **4a:** a rotation-prefix block inside `invDarts G₁`, whose complement still holds a dart outside
  `invDarts G₁`, is `invDarts` of a cell arc of `Π_i`;
* **4b:** an outside walk lying entirely in `invDarts G₁` is, after a rotation, one cell arc;
* the same two clauses for `G₂` and `Π_j`.

`FourPieceWitness.arcsAudit_of_arcs` shows that it follows from the old statement.
`FourPieceWitness.arcAuditResidual_of_planar_noninterleave_arcsAudit`
(`FourPieceWitnessArcsProof.lean`) shows that together with the planar and noninterleaving
statements it gives the corrected residual.

## Truth check (on paper)

* **M2.**  4a is vacuous, because the walk is all `G₁`.  4b holds: `turn_next` steps from `λ_k`
  to `facePerm λ_k = λ_{k+1}`.  At `x` it skips `μ₁`, `e` and `αd₁`, which are not kept, and it
  returns to `λ₁`.  So some rotation of the walk is `G₁`.
* **M5** (a `b`-chord inside `λ`).  The chord meets `v`, since `b` is joined through `v`.  The part
  of the loop away from `C` is joined to `b` by an edge, so it is cut.  The `G₁` block is a prefix
  or a suffix of `λ`, so it is an arc.
* **M6** (an `a`-lobe `A'` in a `G₁`-loop at `v`, between two `F`-corners `Q` and `R`).
  * The boundary cycle of `a` passes `v` twice.  Its piece from `v` to the junction `v₀` of
    `a.arc` and `G₁`, together with `G₁` from `v₀` to `v`, closes off the corner `Q` or the
    corner `R`.
  * That region is bounded by walk edges and `a`-edges, so it misses the `Q₀`-class of `C` unless
    it contains `C`.  It is edge-joined to `a`, so it is cut.
  * So only one of `Q` and `R` is in `F`, and the `G₁ → G₁` jump across `A'` never happens.
  * The clause-2' exemption of the corrected residual is needed for other face sets, not for
    `witnessFaces`.
* **General mechanism** (lane 21c).  A `G₁ → G₁` jump `p → q` in the walk that is not `facePerm`
  forces `facePerm p` to be not kept.  So `Π_i` is pinched at the vertex, and `F` lies in the loop
  of `Π_i` from `q` to `p`.  A dart of the walk off `G₁` inside that loop is an `a`- or `b`-edge
  there, and it joins through `v`.  Then the far side is cut, as in M5 and M6.

**Riskiest point:** the general mechanism for a loop of `G₁` holding both an `a`-lobe and a
`b`-lobe through the same `v`.  Also, M7 (lane 21c) has no bridge-free witness walk at all.  That
does not affect this statement, which is universal over walks, but it is a risk for
`PocketFourPieceWitnessPlanarStatement`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Clauses 4a and 4b for the cut-down witness.**  See the module docstring. -/
def ArcsAuditStatement : Prop :=
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
            invDarts X (outerWalk.rotate n) = invDarts X A.darts)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.ArcsAuditStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
