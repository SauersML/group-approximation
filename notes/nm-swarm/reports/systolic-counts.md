# systolic-counts lane report

Lane `systolic-counts` (clone `stw-fix`).  Roster target: make the red `GGT/SystolicDiscCounts` green and
close it.  Also: the filling inputs `ha hb hc hd` of `fillingStatement_of_simplyConnected`
(`GGT/SystolicDiscFilling.lean:126`), and `hcount hsum` of the alternative Kotowski–Ollivier route.

## 09-13 status

### Roster target: closed on main, no edit needed

* `GGT/SystolicDiscCounts` is no longer red.  go-sr1's 4c12845a1 (09-12 10:34) fixed it together with
  `GGT/SystolicDiscFilling`: probe 0912-103604-11425 (base 3221a02ea) was green, md5 Counts 3330bc17,
  Filling f5f0eb23.  Those bytes are the bytes on main now.
* Current-infrastructure evidence: ko-closed's probe 0913-011617-71747 (base e499fdc3e, record
  `lanes/ko-closed.green.0913-011617-71747`) built `Kazhdan.KotowskiOllivierClosed` GREEN.  That module
  imports `Kazhdan.GHBHyperbolicDiscCounts`, which imports Counts, Filling, `SystolicDiscMovesChord` and
  `SystolicDiscMovesAdapter`.  Every `#audit_axioms` line in them passed.
* Closed endpoints, each followed by `#audit_axioms`:
  * `TriangulatedDisc.exists_typedCounts` (HC11) and `TriangulatedDisc.abs_boundarySum_le` (HC12),
    `GGT/SystolicDiscCounts.lean:417-418`;
  * `TriangulatedDisc.oneEdge` (HC2), `fillingStatement_of_simplyConnected` (HC4) and
    `exists_leastDisc_typedLinks_of_simplyConnected`, `GGT/SystolicDiscFilling.lean:162-164`.

### HC3(d), pinch case, for every triangle complex: closed

kh-torsion handed this lane the pinch case of `ZipSpurStatement`.  kh-torsion keeps `CycleDisc.zip_fold`
and the assembly `zipSpurStatement_of_zipPinch` (`GGT/SystolicDiscZip.lean`, on main at 9445c7860).
kh-torsion wires the endpoint and queues both modules.

* Prop (kh-torsion's, `GGT/SystolicDiscZipFold.lean:281`, on main):
  `ZipPinchStatement X`.  It covers the case where the corners before `du` and after `dv` lie at one
  vertex, `SameCycle σ (α p) (α dv)`.
* Producer: `Systolic.zipPinchStatement (X : TriangleComplex V) : ZipPinchStatement X` in the new module
  `GGT/SystolicDiscZipPinch.lean` (this lane), landed at d74b84054.
  * Probe 0913-023335-5925 (base 3e9636d74) is GREEN on the landed bytes (md5 fbbf5f90, record
    `lanes/systolic-counts.green.0913-023335-5925`).
  * `#audit_axioms` passed on `isFaceCycle_of_map_injective`, `exists_map_val_eq`, `CycleDisc.zip_pinch`
    and `zipPinchStatement`.  `zipPinchStatement` depends on axioms `[propext, Classical.choice,
    Quot.sound]`.
  * The modules it imports did not change between 3e9636d74 and origin/main 4a9981630.
* Proof:
  * split the vertex (`FoldMap.joined D.map p dv`), which has Euler characteristic 4
    (`PinchLemma.split_euler`);
  * `du` does not reach `p` (`PinchLemma.not_reach_p`), and every dart is reached from `du` or from `p`
    (`PinchLemma.reach_or_reach`);
  * so the part reached from `p` (`CycleDisc.pinchMap`) is planar
    (`CombMap.restrict_planar_of_euler_four`);
  * its exterior cycle is `t ++ s` (`PinchLemma.split_isFaceCycle_rest`), lifted to the subtype and
    rotated to read `s ++ t`;
  * every other dart is off the old exterior cycle.  There the split map rotates faces as the old map
    does, so its faces are old interior triangles.

## Brief items

| input | producer on main | state |
|---|---|---|
| `ha : AttachTriangleStatement X` | `Systolic.attachTriangleStatement`, `GGT/SystolicDiscMovesChord.lean:298` | closed (kh-torsion) |
| `hb : InsertChordStatement X` | `Systolic.insertChordStatement`, `GGT/SystolicDiscMovesChord.lean:254` | closed (kh-torsion) |
| `hc : AttachPendantStatement X` | `Systolic.attachPendantStatement`, `GGT/SystolicDiscMovesAdapter.lean:136` | closed (kh-torsion) |
| `hd : ZipSpurStatement X` | `Systolic.zipSpurStatement_of_zipPinch`, `GGT/SystolicDiscZip.lean` | its one input `ZipPinchStatement X` is closed (`Systolic.zipPinchStatement`, this lane, green); kh-torsion wires the closed endpoint |
| `hcount` | `CCKW.typedCountStatement_cosetComplex`, `Kazhdan/GHBHyperbolicDiscCounts.lean` | closed (kh-hyperbolic) |
| `hsum` | `GHBHyperbolicStokes.boundarySumStatement`, `Kazhdan/GHBHyperbolicDiscCounts.lean:56` | closed (kh-hyperbolic) |

## Residual Props

* None from this lane.
* `Systolic.MirrorFoldStatement CCKW.cosetComplex` (HC6, `GGT/SystolicDisc.lean:432`), owned by
  fff-periodic (`GGT/SystolicDiscMirrorFold.lean`).
* ko-closed's `kotowskiOllivier_of_leaves` (c5a8ae8fb, green) consumes it and `ZipSpurStatement` through
  `isHyperbolicGroup_ghb7_of_zipFold`.

## Wiring

* `GGT.SystolicDiscCounts`, `GGT.SystolicDiscFilling`, `GGT.SystolicDiscMovesChord` and
  `Kazhdan.GHBHyperbolicDiscCounts` are not yet reachable from the root.  This lane queued
  `GroupApproximation.GGT.SystolicDiscCounts systolic-counts 4c12845a1`.
* kh-torsion queues `GGT.SystolicDiscZipPinch` with `GGT.SystolicDiscZip`.  Root-wire wave 2
  (wire-queue line 382) already carries `SystolicDiscZip`.
* Stale notes:
  * wire-queue line 318, "GHBHyperbolicDiscCounts waits on red Filling/Counts";
  * the `EdgeInsertion.embed_injective` hold on `EdgeInsertionFaceCycles` and `SystolicDiscMovesChord`,
    because 6a5f25704 renamed the lemma to `embed_injective_faceCycles`;
  * census2 line 52, "red `GGT/SystolicDiscCounts`".

### Current item: HC6, pinched case (`MirrorFoldPinchedStatement X`), one step, offer pending

The lead assigned a piece of `MirrorFoldPinchedStatement X` (`GGT/SystolicDiscMirrorFoldCases.lean:102`).
fff-periodic owns it: the staging layer `FoldStage` and `deleteDigon` are on main (d6f6ccc19, c88b8c1db).
This lane offered fff-periodic the vertex-split step and writes no Lean until they answer.

* Proposed file: `GGT/SystolicDiscMirrorFoldSplit.lean`, importing `SystolicDiscMirrorFoldStage`,
  `VanKampen.PinchLemma` and `VanKampen.CombMapInvariantRestrict`.
* Proposed interface: `FoldStage.exists_split_pinch`.
  * Input: a planar stage `S` whose pending darts are exactly a face cycle `[x₁, x₂, x₃, x₄]`, with the
    ends of `x₁` and `x₃` at one vertex.
  * Output: a planar stage `T` with a pending digon and nothing else pending, the same boundary, and
    `T.map.faceCount ≤ S.map.faceCount`.
* fff-periodic keeps the edge-deletion stage and the assembly.
* If fff-periodic declines, this lane takes an unstarted `PlanarRunInput` case (W1 Lemma 9.4) from
  hull-unbound.

## Next

* kh-torsion has the green SHA and wires the closed `ZipSpurStatement X` endpoint.
* Settle the file name and interface with fff-periodic, then write and probe the split module.
