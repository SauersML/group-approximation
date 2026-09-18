import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessNoninterleaveStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-27: audit of the witness four-block residual

Lane gl-p07-27.  The target is `FourPieceWitness.FourBlockStatement`
(`FourPieceWitnessNoninterleaveStatement.lean`, lane gl-p07-24).  The context is Osin,
arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## VERDICT: THE TARGET IS FALSE

**`FourPieceWitness.FourBlockStatement` is FALSE.**  The counterexample is model M9 below.  M9 also
refutes `PocketFourPieceWitnessNoninterleaveStatement` (`FourPieceWitnessRead.lean`).  So every
route through either statement proves nothing as it stands, for example:
* `noninterleave_of_fourBlock` (`FourPieceWitnessNoninterleaveEndpoint.lean`);
* `arcAuditResidual_of_noPlanarDegenerate_noninterleave_arcsAudit` and
  `arcAuditResidual_of_noPlanarDegenerate_fourBlock_arcsAudit` (`FourPieceNoPlanarProof.lean`).
The failure is that `RegionCandidate` has no nondegeneracy field.  The corrected statements below
add the nondegeneracy that `RealizedSectionFamily.nondegenerate` supplies upstream.

## Model M8 (lane gl-p07-23): vacuous here

In M8 the candidate `a` has both cell arcs empty and `rightSide = []`.  Its `leftSide` is a simple
loop `ℓ` bounding a disc island inside the pocket.  The witness `F` is the pocket minus the island,
which is an annulus.
* **No outer walk.**  `EnclosedFaceSetSucc` turns to its successor, so `outerWalk` is a single
  restricted face orbit.  The boundary of an annulus has two orbits, and `mem_iff` needs both.  So
  there is no `outerWalk`, and the target holds vacuously in M8.
* **Variant M8'** (the island touches `Π_i` at one vertex `v`).  Around `v`, the two complement
  corners (`Π_i` and the island) are separated by corners of `F`.  So `turn_next` keeps the `Ḡ₁`
  orbit apart from the `ℓ̄` orbit, and `mem_iff` fails again.  Vacuous.

## Model M9: a counterexample

Start from M8 (`Π_i` and `Π_j` touch at a vertex `w`, and `b` is an ordinary strip with a nonempty
far side), and change the island.
* **The candidate `a`.**
  * Source `i`, target `j`, both cell arcs empty, `rightSide = []`.
  * `a.1` is a disc of cells inside the pocket, attached to `Π_i` along an edge segment `E` in the
    middle of `G₁`.  Write `G₁ = G₁a · E · G₁b`, with `G₁a` and `G₁b` nonempty.
  * `leftSide = ℓ = a.sideFrom j` is the boundary loop of the disc, and `ℓfree = ℓ \ E` runs
    freely in the pocket.
  * This is a valid `ContiguityGeometry`: one boundary cycle, a disc shelling, `eps` large.
    `JoinsCells` reads only the source and target indices.
* **The pocket walk `K`** is the one of M8.
  * `K.secondSide = a.sideFrom i = []` and `K.firstSide = b.sideFrom j`.
  * `sideFaces K = a.1 ∪ P₀`, where `P₀` is the rest of the pocket.  Both sides are discs, so
    `hinner` and `houter` hold.
  * Take a relator cell `C ∈ P₀`.
* **The witness is `F = P₀`.**
  * The class `keepClass C` is `P₀`, since the edges of `ℓfree` are kept.
  * The component of `a.1` off the block is `a.1` itself: it meets `Π_i`, which lies in
    `sideOutside`.  The faces of `b` lie in `sideOutside`.  So `cut = a.1`.
  * The open faces are `P₀`, which is connected by edges, so `F = P₀`.
  * `F` is a disc whose boundary is a simple cycle.
* **A bridge-free successor outer walk exists**, by `exists_enclosedFaceSetSucc_of_connected`
  (`FourPieceWitnessPlanarWalk.lean`):
  * (A) holds, since the complement of `F` is edge-connected: `a.1` meets `Π_i` along `E`, and `b`
    meets `Π_i`;
  * (B) holds, since the boundary of `F` is one simple cycle;
  * the walk has no bridges.
* **The reading.**  `l = invDarts X outerWalk` reads, cyclically, `Ḡ₁a · ℓ̄free · Ḡ₁b · Ḡ₂ · B̄`.
  * The `ℓ̄free` darts `e` are in class `A`.  `faceOf (α e)` is a face of `a.1`, which is not
    `Π_i`, not `Π_j`, and not in `b.1`.
  * So the cyclic class word is `1 A 1 2 B`.
* **The target fails.**  In a four-block form every `G1` entry lies in `U₁`, so the `G1` entries
  form one cyclic run.  Here they form two runs.
* **The noninterleave statement fails.**  The rotation starting at `Ḡ₁b` has the sublist
  `[g₁b, g₂, g₁a, ℓfree]`, with classes `1 2 1 A`.  This alternates for the predicate
  `e ∈ invDarts G₁`, against its first `CyclicNoInterleave` fact.

**Root cause.**  The docstring of gl-p07-24 (step 1 and step 2) reads `l` as a sub-walk of the
pocket curve `Γ = Ḡ₁ · Ā · Ḡ₂ · B̄`.  Step 1 is correct: every entry of `l` is in one of the four
arcs.  Step 2 uses that `Γ` bounds the pocket, so that `F`'s boundary follows `Γ` in cyclic order.
With empty contact arcs this fails.  The far side of `a` is then its whole boundary, so it is not
anchored between `G₁` and `G₂`.  In M9 it is read in the middle of `G₁`.

## The corrected statements

* `FourPieceWitness.FourBlockNondegStatement`: the target, with four extra hypotheses after
  `Disjoint a.1 b.1`:
  `0 < (a.cellArcList i).length`, `0 < (a.cellArcList j).length`,
  `0 < (b.cellArcList i).length`, `0 < (b.cellArcList j).length`.
* `FourPieceWitness.NoninterleaveNondegStatement`: `PocketFourPieceWitnessNoninterleaveStatement`,
  with the same four hypotheses.

Upstream, `RegionCandidate.cellArcList_length_pos` (`OsinPocketCellWalk.lean`) turns
`RealizedSectionFamily.nondegenerate` into these hypotheses.  But
`InnerPocketEnclosedTwoArcStatement` (`P07LakeExclusion/InnerTwoArcLong.lean`) has no
nondegeneracy premise.  **A route to it through these statements must add the hypotheses there.**

## Truth check of the corrected statements

**TRUE; no counter-model found.**
* With all four arcs nonempty, `a.sideFrom j` starts at the end of `a`'s arc on `Π_i`, where `G₁`
  starts.  It ends at the start of `a`'s arc on `Π_j`, where `G₂` ends.  The same holds for `b`.
  So `Γ` is a closed curve made of four anchored arcs.
* A region touching the middle of an arc (like the blob of M9) is now linked to its own contact
  arcs, so it encloses a sub-pocket between the two contacts.  That sub-pocket is either cut or
  read as a cyclic interval of `Γ`, which is step 2 of gl-p07-24.
* **Checked models** (with nondegenerate candidates):
  * the `a`-bulge along the start of `G₁`;
  * the `a`-horseshoe touching the middle of `G₁` along an edge segment, with `C` on either side;
  * the same horseshoe touching `Π_i` at a single vertex, where `F` is a figure eight;
  * `a` pinched at a vertex to a blob that touches `G₁`;
  * all the models of gl-p07-24 whose arcs are nonempty.
  Each reads four blocks, or has no outer walk.
* **M9 is excluded**, since `0 < (a.cellArcList i).length` fails there.  M8 is also excluded.

## Why the corrected statements are strictly weaker

* **Strictly weaker.**  Each one follows from its original by ignoring the four extra hypotheses
  (`fourBlockNondeg_of_fourBlock` and `noninterleaveNondeg_of_noninterleave`,
  `FourBlockWitnessWeaken.lean`).  They are not restatements: M9 refutes each original, but it
  fails the hypothesis `0 < (a.cellArcList i).length`, so it does not refute the corrections.
* **Reduction.**  `noninterleaveNondeg_of_fourBlockNondeg` (`FourBlockWitnessWeaken.lean`) proves
  the corrected noninterleave statement from the corrected four-block statement.
  `FourBlockWitnessLabel.lean` proves step 1 and isolates the smaller residual.
-/
