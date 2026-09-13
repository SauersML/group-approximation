# systolic-counts lane report

Lane `systolic-counts` (clone `stw-fix`).  Roster target: make the red `GGT/SystolicDiscCounts` green and
close it.  Also: the filling inputs `ha hb hc hd` of `fillingStatement_of_simplyConnected`
(`GGT/SystolicDiscFilling.lean:126`), and `hcount hsum` of the alternative Kotowski–Ollivier route.

## 09-13 status: target closed on main, no edit needed

* `GGT/SystolicDiscCounts` is no longer red.  go-sr1's 4c12845a1 (09-12 10:34) fixed it together with
  `GGT/SystolicDiscFilling`: probe 0912-103604-11425 (base 3221a02ea) was green, md5 Counts 3330bc17,
  Filling f5f0eb23.  Those bytes are the bytes on main now.
* Current-infrastructure evidence: ko-closed's probe 0913-011617-71747 (base e499fdc3e, record
  `lanes/ko-closed.green.0913-011617-71747`) built `Kazhdan.KotowskiOllivierClosed` GREEN.  That module
  imports `Kazhdan.GHBHyperbolicDiscCounts`, which imports Counts, Filling, `SystolicDiscMovesChord` and
  `SystolicDiscMovesAdapter`.  Every `#audit_axioms` line in them passed.
* No module in the 911-module import closure of `Kazhdan.GHBHyperbolicDiscCounts` has changed between
  df2f3b1a8 and main be2d727a9.  The `lakefile.toml` change in that range only adds the Bowen–Chapman Palomar
  libraries to `defaultTargets`.  So this lane ran no probe (rule 20).
* Closed endpoints, each followed by `#audit_axioms`:
  * `TriangulatedDisc.exists_typedCounts` (HC11) and `TriangulatedDisc.abs_boundarySum_le` (HC12),
    `GGT/SystolicDiscCounts.lean:417-418`;
  * `TriangulatedDisc.oneEdge` (HC2), `fillingStatement_of_simplyConnected` (HC4) and
    `exists_leastDisc_typedLinks_of_simplyConnected`, `GGT/SystolicDiscFilling.lean:162-164`.

## Brief items

| input | producer on main | state |
|---|---|---|
| `ha : AttachTriangleStatement X` | `Systolic.attachTriangleStatement`, `GGT/SystolicDiscMovesChord.lean:298` | closed (kh-torsion) |
| `hb : InsertChordStatement X` | `Systolic.insertChordStatement`, `GGT/SystolicDiscMovesChord.lean:254` | closed (kh-torsion) |
| `hc : AttachPendantStatement X` | `Systolic.attachPendantStatement`, `GGT/SystolicDiscMovesAdapter.lean:136` | closed (kh-torsion) |
| `hd : ZipSpurStatement X` | none | OPEN (kh-torsion) |
| `hcount` | `CCKW.typedCountStatement_cosetComplex`, `Kazhdan/GHBHyperbolicDiscCounts.lean` | closed (kh-hyperbolic) |
| `hsum` | `GHBHyperbolicStokes.boundarySumStatement`, `Kazhdan/GHBHyperbolicDiscCounts.lean:56` | closed (kh-hyperbolic) |

`GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold` (`Kazhdan/GHBHyperbolicDiscCounts.lean:84`) already supplies
`ha hb hc`, `CCKWTits.cckwCosetComplex_simplyConnected`, `hcount` and `hsum`, so this route has exactly two
open inputs.

## Residual Props (owned by other lanes)

* `Systolic.ZipSpurStatement CCKW.cosetComplex` (HC3(d), `GGT/SystolicDisc.lean:421`), owned by kh-torsion
  (roster target `zipSpur_cosetComplex`, `GGT/SystolicDiscZip.lean`, not on main).  The fold case
  `CycleDisc.zip_fold` is on main unprobed (3e86a1d89, `GGT/SystolicDiscZipFold.lean`).  kh-torsion's
  probe 0913-011705-84703 of it failed.
* `Systolic.MirrorFoldStatement CCKW.cosetComplex` (HC6, `GGT/SystolicDisc.lean:432`), owned by
  fff-periodic (`GGT/SystolicDiscMirrorFold.lean`, not on main).
* ko-closed's `kotowskiOllivier_of_leaves` (c5a8ae8fb, green) consumes both through
  `isHyperbolicGroup_ghb7_of_zipFold`.

## Wiring

* `GGT.SystolicDiscCounts`, `GGT.SystolicDiscFilling`, `GGT.SystolicDiscMovesChord` and
  `Kazhdan.GHBHyperbolicDiscCounts` are not yet reachable from the root.  This lane queued
  `GroupApproximation.GGT.SystolicDiscCounts systolic-counts 4c12845a1`; root-wire's initial queue had
  "SystolicDiscCounts once green".
* Stale notes:
  * wire-queue line 318, "GHBHyperbolicDiscCounts waits on red Filling/Counts";
  * the `EdgeInsertion.embed_injective` hold on `EdgeInsertionFaceCycles` and `SystolicDiscMovesChord`,
    because 6a5f25704 renamed the lemma to `embed_injective_faceCycles`;
  * census2 line 52, "red `GGT/SystolicDiscCounts`".

## Next

This lane's scope is done, and the lead has been asked for the next item.
