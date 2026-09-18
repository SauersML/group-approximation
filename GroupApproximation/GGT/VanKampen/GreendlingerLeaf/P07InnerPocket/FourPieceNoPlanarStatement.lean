import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcAuditStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessDef
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-28: the corrected residual without the planar statement

The context is Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  The target is
`PocketFourPieceArcAuditResidualStatement` (`FourPieceArcAuditStatement.lean`, lane gl-p07-21c).

## Why a new route

Lane gl-p07-25 reduced the target to three statements
(`FourPieceWitness.arcAuditResidual_of_planar_noninterleave_arcsAudit`).  One of them,
`PocketFourPieceWitnessPlanarStatement`, is FALSE: model M8, lane gl-p07-23,
`FourPieceWitnessPlanarAudit.lean`.  So that route proves nothing.  This lane replaces the planar
statement by a case split.

## The case split

Write `F = witnessFaces a b K C.face`, and call a *witness walk* a list `outerWalk` with
`EnclosedFaceSetSucc X F outerWalk` and `faceOf (α d) ∈ F` for every `d ∈ outerWalk` (no bridges).

* **(i) A witness walk exists.**  This case is proved.  Branch 1 of the target holds with
  `faces = F`:
  * `C.face ∈ F` is `mem_witnessFaces_self`;
  * `F ⊆ sideFaces K.walk` is `witnessFaces_subset_sideFaces`;
  * clause 2' is the third disjunct, from `dart_clause`;
  * clause 3 is `PocketFourPieceWitnessNoninterleaveStatement`;
  * clauses 4a and 4b are `FourPieceWitness.ArcsAuditStatement`.
  Both statements are universal over witness walks, so they apply to this walk.
* **(ii) No witness walk exists.**  This case is the residual
  `FourPieceWitness.NoPlanarDegenerateStatement` below.  By
  `witnessFaces_enclosedFaceSetSucc_of_connected` (lane gl-p07-23), hypothesis (A) or (B) fails
  in this case (`FourPieceWitness.not_connected_of_not_exists_walk`, `FourPieceNoPlanarProof.lean`).
  So case (ii) is the degenerate M7/M8 case the lane asked about.

Splitting on the existence of a witness walk, not on (A) ∧ (B), makes the residual hypothesis
stronger ("no witness walk" implies "not (A) ∧ (B)"), so the residual is weaker.

## The residual (`FourPieceWitness.NoPlanarDegenerateStatement`)

It has the premise block of the target, plus the hypothesis that `F` has no witness walk.  Its
conclusion is the target's conclusion.

**Strictly weaker and strictly smaller.**
* The target implies it (`FourPieceWitness.noPlanarDegenerate_of_arcAuditResidual`): just drop
  the extra hypothesis.
* It asserts nothing in the models where a witness walk exists, such as M2, M5 and M6.  There
  the target still asserts branch 1.  Those models are covered by the proved case (i) plus the
  two universal statements.
* The false planar statement also implies it, vacuously
  (`FourPieceWitness.noPlanarDegenerate_of_planar`).  So it does not add anything the planar
  route needed.

**Endpoints** (`FourPieceNoPlanarProof.lean`):
* `FourPieceWitness.arcAuditResidual_of_noPlanarDegenerate_noninterleave_arcsAudit`;
* `FourPieceWitness.arcAuditResidual_of_noPlanarDegenerate_fourBlock_arcsAudit`, the same with
  `FourBlockStatement` (lane gl-p07-27) in place of the noninterleaving statement, through
  `noninterleave_of_fourBlock`.

## Truth check (on paper)

The residual follows from the target, so any model of the target is a model of the residual.  The
models of lanes 21c, 23 and 25 sort as follows.

* **M2 (crescent).**  `F = {C}`.  The complement of `{C}` is edge-connected and `∂C = λ` is
  connected, so (A) and (B) hold and a witness walk exists (the loop `λ`).  So M2 is case (i),
  and the residual is vacuous there.  Case (i) needs clause 3, which is trivial because the walk
  is all `G₁`, and 4b, which lane 25 checked.
* **M5 (a `b`-chord inside `λ`)** and **M6 (an `a`-lobe behind a `G₁`-loop edge).**  Lanes 24 and
  25 read their witness walks (`λ̄ · Ā'` for M6).  So they are case (i) and the residual is
  vacuous.  Should a witness walk fail to exist in some variant, the residual's conclusion there
  is the target's conclusion, which lane 21c checked.
* **M7 (the `a/Π_j/b` blob behind the pinch `v`).**  The witness has no walk: that is how lane 23
  refuted the planar statement through `dart_clause`.  So M7 is case (ii).  The residual holds
  through branch 2, with `faces = R`, the region bounded by one cell arc of `i` (lane 21c).
* **M8 (empty-arc island).**  `F` is an annulus, and there is no walk (lane 23).  So M8 is case
  (ii).  The residual holds through branch 1 with `faces = P' ∪ a.1`: the inner pocket together
  with the island `a.1`.
  * The walk reads the boundary of a disc, `Ḡ₁ · B̄ · Ḡ₂`, where `B̄` is the far side of `b`.
    `ℓ = a.sideFrom j` is interior, so it is not on the walk.
  * Clause 2' holds: every `α d` is a `G₁`, `G₂` or far-side dart whose face is in `P'`.
  * Clause 3 holds: the cyclic word has the four-block form `G1 · B · G2 · []`.
  * Clause 4a holds: an all-`G₁` rotation prefix with a non-`G₁` entry left over is a contiguous
    piece of the `G₁` block, so it is a sub-arc of `Π_i`, possibly empty.  The same holds for `G₂`.
  * Clause 4b is vacuous.

**No model found refutes the residual.**  It inherits the target's riskiest point: clause 4a at
other pinch pathologies in case (ii).

## Dependencies still open

* `PocketFourPieceWitnessNoninterleaveStatement`, or `FourPieceWitness.FourBlockStatement`
  (lane gl-p07-27);
* `FourPieceWitness.ArcsAuditStatement` (lane gl-p07-29);
* `FourPieceWitness.NoPlanarDegenerateStatement` (this file).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness
