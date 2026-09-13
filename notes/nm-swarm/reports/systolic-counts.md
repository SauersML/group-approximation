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

### HC6, pinched case: offer withdrawn

hfold is closed: fff-periodic's `Systolic.mirrorFold (X) : MirrorFoldStatement X`
(`GGT/SystolicDiscMirrorFold`, 426813b24, probe 0913-052528-4751).  The vertex-split step offered to
fff-periodic (`FoldStage.exists_split_pinch`) is not needed.  This lane wrote no Lean for it.

### Current item: W1, one (c) transport glue module for go-lemma42

The lead assigned this lane one of go-lemma42's (c) transport modules for `OsinMultipleEdgeCut.ofPocketRegion`.
The candidates are `GGT/VanKampen/SurgeryPocketGlue`, `SurgeryPocketGluePlanar`,
`Estimating/OsinPocketGlueDiagram` and `Estimating/OsinPocketGlueTransport`.

* Route: glue an O-equivalent copy Ξ into Δ' along the region cycle and build the diagram with
  `DiscDiagram.ofPlanar`.  Planarity comes from an χ count through `MapCollapse.reclosed_isRestriction`.
* Proposed module for this lane: `SurgeryPocketGluePlanar`.  This lane asked go-lemma42 for the exact
  statement and writes no Lean until the answer.
* Planned count, for `Seam.glueMap` (go-lemma42's unlanded `SurgeryPocketGlue`):
  * darts: the glued darts are the interior darts of `faces` plus the darts of `X` (`Seam.splitEquiv`);
  * faces: `faces.card` old faces plus the faces of `X` other than `outer`.  The reclosed map has
    `faceCount + faces.card = M.faceCount + 1` (`reclosedMap_faceCount`);
  * vertices: the vertices of `X` (first return, `Seam.glue_isRestriction`) plus the vertices of `M` whose
    darts are all interior.  The reclosed map keeps the vertices of `M` that meet a kept dart
    (`reclosedMap_vertexCount`);
  * so χ(glued) − χ(X) = χ(M) − χ(reclosedMap M faces boundary).  With `M` and `X` planar and
    `reclosedMap_planar`, χ(glued) = 2;
  * connectedness: lift paths of `M` to the glued map, as `reclosedMap_connected` does.

## Brief items

| input | producer on main | state |
|---|---|---|
| `ha : AttachTriangleStatement X` | `Systolic.attachTriangleStatement`, `GGT/SystolicDiscMovesChord.lean:298` | closed (kh-torsion) |
| `hb : InsertChordStatement X` | `Systolic.insertChordStatement`, `GGT/SystolicDiscMovesChord.lean:254` | closed (kh-torsion) |
| `hc : AttachPendantStatement X` | `Systolic.attachPendantStatement`, `GGT/SystolicDiscMovesAdapter.lean:136` | closed (kh-torsion) |
| `hd : ZipSpurStatement X` | `Systolic.zipSpurStatement` and `CCKW.zipSpur_cosetComplex`, `GGT/SystolicDiscZip.lean:122,131` | closed (kh-torsion, 8389a0e6c, probe 0913-030432-13308), from `Systolic.zipPinchStatement` (this lane) |
| `hcount` | `CCKW.typedCountStatement_cosetComplex`, `Kazhdan/GHBHyperbolicDiscCounts.lean` | closed (kh-hyperbolic) |
| `hsum` | `GHBHyperbolicStokes.boundarySumStatement`, `Kazhdan/GHBHyperbolicDiscCounts.lean:56` | closed (kh-hyperbolic) |
| hfold `MirrorFoldStatement X` | `Systolic.mirrorFold`, `GGT/SystolicDiscMirrorFold` | closed (fff-periodic, 426813b24) |

## Residual Props

* None from this lane.

## Wiring

* `GGT.SystolicDiscCounts`, `GGT.SystolicDiscFilling`, `GGT.SystolicDiscMovesChord` and
  `Kazhdan.GHBHyperbolicDiscCounts` are not yet reachable from the root.  This lane queued
  `GroupApproximation.GGT.SystolicDiscCounts systolic-counts 4c12845a1`.
* kh-torsion queued `GGT.SystolicDiscZipPinch systolic-counts d74b84054` and
  `GGT.SystolicDiscZip kh-torsion 8389a0e6c`.  The root imports `GGT.SystolicDiscZip` since c72bdfd5d,
  and `SystolicDiscZip` imports `SystolicDiscZipPinch`, so this lane's module is in the root closure.
* Stale notes:
  * wire-queue line 318, "GHBHyperbolicDiscCounts waits on red Filling/Counts";
  * the `EdgeInsertion.embed_injective` hold on `EdgeInsertionFaceCycles` and `SystolicDiscMovesChord`,
    because 6a5f25704 renamed the lemma to `embed_injective_faceCycles`;
  * census2 line 52, "red `GGT/SystolicDiscCounts`".

## Next

* Get the module and statement from go-lemma42.  Then write the module, land it unverified, probe it,
  fix it until green, and message go-lemma42 and main.
