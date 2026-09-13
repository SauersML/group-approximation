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

### W1 pocket glue: cancelled

The lead cancelled the handout.  go-lemma42 wrote `SurgeryPocketGlueVertices`, `SurgeryPocketGlueCount`
and `SurgeryPocketGluePlanar` itself.  This lane wrote no Lean for W1.

### Current item: two defects in the non-MF verifier, landed at 736f7ea44

census found both defects in `scripts/check_non_mf_unconditional.py`.  The script has no owner, so the lead
gave this item to this lane.  Landed with `NM_UNVERIFIED=1`; the script is not in
`lanes/systolic-counts.files`.

* False red on hKO.  `resolve` matched a dotted name only against a bare namespace token or a whole
  namespace stack.  `KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed` (inside
  `GroupApproximation.KMSGroup`) concludes `Manuscript.NonMF.TheoremC.KotowskiOllivierStatement`, a partial
  path, so the producer was filed under a name outside the corpus.  Fix: `resolve_written_name` tries each
  prefix of the declaration's namespace followed by the name against the corpus full names, as Lean does.
  `_unfold` and `classify` resolve with the namespace.  Nothing matches on a shared tail.
* Blind spot on in-place constructions.  `HullSC.CutLift` is built by `have hcl : CutLift … := { … }` in
  `letterStepBound_of_cutLiftOutcome`, and rows 8aead549f1fe and 4895f03fdf5f reported no producer.  Fix:
  `in_place_heads` reads `have`/`haveI`/`let`/`letI [name] : T := ⟨…⟩ | { … }` and `(⟨…⟩ : T)`,
  `({ … } : T)`; each produces `T` under the declaration's requirements and taint.  Refutations and
  sort-valued defs produce nothing this way.
* Calibration on MSI, through a copy of census's `census_run.sh`, on an export of 9b413742b:
  * `PRODUCER_FIXTURE`, now part of `--self-test`: the old script got 7 of its 11 consumers wrong, the
    candidate gets 11 of 11 right.  A Prop with no producer still reports red, a producer resting on
    `sorry` still reports conditional-debt, and the partial-path and in-place shapes come out clean.
  * `--self-test`, the importers' self-tests and `check_ledger_unconditional` pass.  The gate reports 47
    cited declarations unconditional before and after.
* Register effect.  `sentence_census --verify-unconditional` exits 1 until census re-registers
  `metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt`.  This is the ratchet working, not a candidate bug.
  * 3 stale lines: `HullTheorem312Lemma58.normalizesNoNontrivialFinite_of_isHyperbolicallyEmbedded`,
    `HullSC.CutLift.toCutMove` and `HullSC.cutLiftOutcome` now report header binders only.
  * 169 new findings (145 open-predicate, 19 carrier-data, 2 inlined-statement, 2 buried-conditional,
    1 conditional-data).  The old resolver dropped the partial path
    `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement`, so the `TheoremC.LiteratureInputs`
    producers over it, `FournierFacioParagraph`, `HullOneStepStatement`, `HullTowerStatementGeneral` and the
    Printed* carriers counted as discharged.
* Trace on MSI, both discharge fixed points compared declaration by declaration:
  * no declaration loses a conclusion or a requirement (0 violations);
  * 35 names gained (producers: 22 in-place, 15 completed conclusions, 24 cascades); spot-checked
    `CutLift`, `KotowskiOllivierStatement`, `Heis`, `IsSpelling`, `LinkCertificateChecks`, all genuine;
  * 51 names lost, each blocked by a Prop undischarged under both scripts:
    `RelativeGreendlingerQuasiGeodesicLeastAreaStatement` (143 blocked producers),
    `RelativeGreendlingerQuasiGeodesicStatement` (17), `EstimatingUnboundOutputStatement` (11),
    `EstimatingSelectionConstructionStatement` (11), `RelativeGreendlingerStatement` (1).
* Sent to census and main: the SHA, the 3 stale lines and the grouped findings.  CI "Sentence-level census"
  (`build-non-mf-pdf.yml`) stays red until census re-registers.

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

* census re-registers the baseline against 736f7ea44.  If a finding there points at the verifier and not at
  the corpus, this lane fixes the script and re-runs the calibration on MSI.
* Otherwise idle until the lead assigns a new item.
