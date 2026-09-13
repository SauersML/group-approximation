# census

Lane `census` of the non-MF every-line swarm (2026-09-13), target U3. The lane owns `metadata/NON_MF_SENTENCE_MAP.tsv`,
`metadata/NON_MF_SENTENCE_CENSUS.{tsv,md}`, `notes/nm-swarm/WORKLIST.md`, and both baseline files. Every census pass
runs on MSI through `$NM/census/census_merge.sh`. The script lands the result only when the merge, write, register,
verify-decls and verify-unconditional passes all exit 0. `--check` fails as long as any row is partial, so it does
not block landing.

## Status: merge 0913-091312 at base 736bfe261, landed de0c922ef

| status | sentences |
| --- | --- |
| `formalized` | 345 |
| `definition` | 53 |
| `structural` | 46 |
| `provenance` | 19 |
| `attribution` | 18 |
| `partial` | 17 |
| **total** | 498 |

- **Verifiers.** `--verify-unconditional` reports 284 conditional or literature-fed assignments, all accepted and 0
  new. `--verify-decls` reports 0 missing of 1183 named declarations.
- **Conditional baseline:** 153 active findings, against 135 at 39dd43b39.
  - Merge 13 (9b413742b) removed 53 stale lines, revised 56 in place and registered 71 new ones. Merges 14 and 15
    changed no line.
  - By kind: 120 `buried-conditional`, 24 `open-predicate`, 6 `carrier-data`, 2 `conditional-data`,
    1 `inlined-statement`.
  - See "Walls" and "register.py since 88289a4ee".
- **Open rows:** 17 partial. See "Open rows".
- **Reachability.** No row carries a `carrier not root-reachable` note. See "Carrier reachability".

## Landings (09-13)

| merge | base | result | partial | baseline findings |
| --- | --- | --- | --- | --- |
| 0913-022302 | d6f6ccc19 | not landed: REGISTER=3, rules added | | |
| 0913-023622 | 63f147d7b | 94bb0a9f8 | 59 | 132 |
| 0913-025455 | f6985a197 | 86df293af: root-wire wave 2 restored 20 rows | 23 | 132 |
| 0913-032518 | a4fd8595c | not landed: REGISTER=3 on the hull-count94 carriers | 26 | |
| 0913-034415 | 5f9c16b7b | 88289a4ee | 26 | 135 |
| 0913-042746 | 395b3c31c | 39dd43b39 | 22 | 135 |
| 0913-043826 | cba3ce8ba | a3e35aece | 26 | 135 |
| 0913-044759 | df84b2475 | a21cc0c19 | 27 | 135 |
| 0913-050040 | 245a1c0c2 | 6fd3d7a55 | 23 | 135 |
| 0913-053204 | e32bac3f3 | not landed: REGISTER=3 (2 unclassified), VERIFY_UNCOND=1 | 18 | |
| 0913-064842 | 45358bab7 | dump only, no landing | 17 | |
| 0913-074521 | 77c9de1d2 | not landed: REGISTER=3 (6 unclassified) | 18 | |
| 0913-085330 | 045b5f849 | 9b413742b | 18 | 153 |
| 0913-090435 | d0a41c1da | 9a13b22c9: dgo-analytic SUPERSEDES row merged in, no register change | 18 | 153 |
| 0913-091312 | 736bfe261 | de0c922ef: root wiring at 559636b4a restored `b6d1590be7ab` | 17 | 153 |

- Merges 8 to 10 changed no baseline line: 377 assignments, all accepted.
- From e32bac3f3 on, register.py finds 53 stale lines.
- Merge 12 stopped on six findings on rows `8aead549f1fe` and `4895f03fdf5f`: `osinLemma94Section_of_planarPieces`,
  its four pieces and `DartMinimal`. They come from sec5-sentences' row (697706d62, 296b0173f). register.py now
  registers them with the text under "Walls".

## Walls of sec:torsion-free (at 045b5f849)

Three of the four walls are closed.

- **hKO.** `TheoremC.KotowskiOllivierStatement` is closed by `KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed`
  (`#audit_closed_axioms`, root-imported, f65f99f17) over `Systolic.mirrorFoldPinched` (426813b24).
- **hbridge.** `RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement` is closed by
  `HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed` (`#audit_closed_axioms`, root-imported, 18682110d).
- **hW.** `FinitelyPresentedInfiniteSimpleStatement` (Hyde-Lodha) is closed by
  `HydeLodha.finitelyPresentedInfiniteSimple_closed` (`#audit_closed_axioms`).

The residual is **hgreendlinger** (`RelativeGreendlingerQuasiGeodesicLeastAreaStatement`), not yet produced.

- Its producers bind one of three things:
  - Osin's Lemma 9.4 (`OsinLemma94SectionStatement`) with the pocket inputs;
  - Osin's Lemma 9.7;
  - the historical `RelativeGreendlingerQuasiGeodesicStatement`.
- The metric half of Lemma 9.4 is closed (`osinLemma94AntiparallelMetric`, e3da1ba60). The diagram half is not yet
  produced. It is `OsinLemma94PlanarRunInput` for `osinLemma94Section_of_pieces`, or four planar pieces for
  `osinLemma94Section_of_planarPieces` (`#audit_axioms`, 80790fad1, root-imported at 559636b4a):

| piece | content | owner |
| --- | --- | --- |
| `OsinLemma94PolygonRealizationInput` | a dart-minimal optimum has maximal component polygons | hull-unbound |
| `OsinLemma94PolygonCountInput` | a side budget K chosen before eps and a slack L chosen after | hull-count94 |
| `OsinLemma94CaseOneInput` | no backwards connector pair onto a side that is not cutting | theoremc-retire |
| `OsinLemma94CaseTwoInput` | no backwards connector pair onto a cutting side | sec5-sentences |

- **DartMinimal.** `GloballyDistinguishedSectionFamily.DartMinimal` is a hypothesis of each piece, not an open
  carrier. `exists_dartMinimal` (80790fad1) and `exists_reduced_dartMinimal` (b6bda9923) produce dart-minimal
  families.
- **Reduced route.** The route over `OsinLemma94PlanarRunInputReduced` (88db0df7b) was retired at b6bda9923.
- **Route refuted.**
  - `Embedded.FaceSetEarStatement` and `FaceSetEarDataStatement` are false (`not_faceSetEarStatement`,
    `not_faceSetEarDataStatement`, 9dda53a05).
  - So is `RegionShellingStatement` (`not_regionShellingStatement`, 3f6eaff76).
  - A baseline line that binds one of them is graded "route refuted; W1 (a) is on the ofPlanar carrier", not open.
- **Forms over hgreendlinger alone.** They are in `TorsionFreeGreendlingerLeaf`, `TorsionFreeGreendlingerSentences`,
  `TorsionFreeGreendlingerForms`, `HullSCGreendlingerForms`, `TheoremCAssemblyGreendlingerLeaf` and `HullCorollary74`.
  All six are root-imported at 559636b4a.

## Classifier defects in verify-unconditional

census found two defects in `scripts/check_non_mf_unconditional.py`. ROSTER-0913 gives both to systolic-counts,
together with a calibration fixture. systolic-counts has owned them since 08:05. Neither fix is on origin at
0793191e3.

- **False red on hKO.**
  - The resolve records a namespace only as the bare token or the full stack path. `kotowskiOllivier_closed` writes
    its conclusion under the partial path `Manuscript.NonMF.TheoremC` inside `GroupApproximation.KMSGroup`, so the
    verifier still reports `KotowskiOllivierStatement` as never produced.
  - 74 findings of the 77c9de1d2 dump name it, and the registered lines say so.
  - At the first merge after the fix, the lines that rest on hKO alone go stale and the rest need a revision.
- **Blind spot.**
  - The producer index has no entry for a Prop structure built by an anonymous constructor (`HullSC.CutLift`,
    `HullSCLemma51LetterPullbackCut.lean:87`).
  - `cutLiftOutcome` and `CutLift.toCutMove` are registered as "not a conditional".

## register.py since 88289a4ee

- **Revisions** (in place; each line keeps its key):
  - hfold, hpinch and hKO closed (426813b24, f65f99f17);
  - hbridge closed (18682110d);
  - the Lemma 9.4 diagram half split into four pieces (80790fad1).
- **New rules:**
  - route refuted, for the FaceSetEar and RegionShelling binders;
  - `HullSC.CutLift`, the classifier blind spot above;
  - the closed bridge endpoints, whose buried premises are the printed hypotheses of the Statement they prove;
  - the closed hKO chain (`KotowskiOllivierClosed.*`, `kotowskiOllivier_of_pinched`);
  - the four planar pieces and `DartMinimal`;
  - Hull Corollary 7.4 (cite-hull, 7f37c80ef):
    - `PrintedHullCorollary74` is the printed statement over `HullSC.HullTowerStatementGeneral`;
    - the premises of `exists_commonQuotient_of_hullGeneratingSet` are printed hypotheses;
  - Hull Lemma 4.4 and the one-step quotients, over the least-area leaves.

## Merge tool changes (09-13)

- **Root-reachability.** A row stays `formalized` or `definition` only when every declaration it names lives in a
  module of the `GroupApproximation` import closure, per COMMON_RULES.
  - A declaration that origin does not define goes to the note as `not defined at origin <sha>: ...`.
  - A declaration that is compiled but outside the closure goes to the note as `carrier not root-reachable at origin
    <sha> (...)`.
  - Either way the row is graded `partial`. The row is recomputed from the lane rows at every merge, so it regains
    its grade once the module is wired.
- **Resolve order.** A row resolves:
  1. by a sentence key quoted in its note;
  2. then by the only candidate;
  3. then by text score with a margin;
  4. then by the unique sentence that starts at its line.

  Otherwise it is skipped as ambiguous.
- **DROP overrides.** `overrides.tsv` accepts `lane<TAB>given key<TAB>DROP<TAB>declarations<TAB>reason`. A row left
  with no declarations is skipped.
- **Justification revisions.** When a premise quoted in a registered line gets closed, register.py rewrites the
  line's justification. The line ends with `[revised by the census merge at <sha>: <reason>]`.
- **Landing.**
  - The script checks the MSI master with `ssh -O check` and runs the passes detached.
  - It lands the map, the census, both baselines and `notes/nm-swarm/WORKLIST.md`, with `NM_BASE` set to the
    export sha.

## Overrides in force

- **Re-keys.** In both rows the note quotes the sentence, and the text match lost only on margin:
  - jacobson `LINE:1147` goes to `b6d1590be7ab`, the GHW / Kazhdan-subgroup sentence;
  - sec3-sentences `LINE:837` goes to `bd35898b630c` ("Since r=vwr+fr ...").
- **Retirements** (lead ruling of 2026-09-13 on debt-conditional groups B and C). All 19 lines were removed at
  94bb0a9f8.
  - sec5-sentences `LINE:1636`, `1644`, `1662`, `1665` and `1698` drop their historical quasi-geodesic and unbounded
    Lemma 4.4 carriers.
  - hull-respell `LINE:1636`/`1644` drop the three `_of_quasiGeodesicLeaves` declarations, and `LINE:1675` drops
    `osin24HullStep_of_boundedLeaves`.

## Rows skipped

- **Resolved.** dgo-analytic `LINE:1688` was ambiguous up to merge 13, with candidates `d8d9d495865d` and
  `8e8d5f3f8be0`. a032ab802 replaced it with a `SUPERSEDES` row, `LINE:1728`, which names key `92115dd7edef`. Merge
  14 merged that row into key `92115dd7edef`, where it joins the rows of baseline-debt, cite-osin and sec5-sentences.
- **hull-respell `LINE:1636` and `LINE:1644`.** The DROP overrides removed every declaration, so both rows are
  skipped.

## Carrier reachability

At d0a41c1da, open rows named nine carrier modules that were compiled but outside the `GroupApproximation` import
closure:

- `Manuscript.NonMF.TorsionFreeGreendlingerLeaf` (14 rows)
- `Manuscript.NonMF.TorsionFreeGreendlingerSentences` (7 rows)
- `Manuscript.NonMF.TorsionFreeGreendlingerForms` (7 rows)
- `GGT.HullSCGreendlingerForms`
- `GGT.VanKampen.Estimating.OsinLemma94PlanarPieces`
- `GGT.VanKampen.Estimating.OsinLemma94DartMinimal`
- `Manuscript.NonMF.TheoremCAssemblyGreendlingerLeaf`
- `Manuscript.NonMF.HullCorollary74`
- `Manuscript.OneSidedMFRadical.JacobsonPresentedKazhdanFinite`

root-wire's 559636b4a wires all nine. Merge 15 cleared every reachability note, and `b6d1590be7ab` (ghw-assembly,
tex 1145) is `formalized` again.

Rows `8aead549f1fe` and `4895f03fdf5f` still name three declarations that origin no longer defines, all retired at
b6bda9923:

- `OsinLemma94PlanarRunInputReduced`;
- `osinLemma94PlanarRunInput_of_reduced`;
- `osinLemma94Section_of_planarRunInputReduced`.

They come from the sec5-sentences row `LINE:1636`, and the merge moves them to the note. The cleanup rides along with
sec5-sentences' next row update.

## Open rows at de0c922ef (17 partial, by owner)

The keys are sentence keys. `notes/nm-swarm/WORKLIST.md` has the full sentences and declarations.

| owner | rows | keys @ tex line |
| --- | --- | --- |
| nm-endpoints | 8 | `a16637da7249`@66, `0f22bdbc4184`@285, `dce7a9ff4e83`@291, `8aead549f1fe` `4895f03fdf5f`@1637, `2f55113239ce`@1651, `7b1fa3182135` `8b1ec28a0e73`@1719 |
| cite-hull | 4 | `a9dd4b90e479`@1629, `bcc99703f838`@1644, `2d1cd22e5f49` `2f997e5af4e6`@1659 |
| cite-hull+kh-ejz+nm-endpoints | 2 | `8097c371f35d` `dab2f2bfe084`@1675 |
| ghw-assembly | 1 | `3009704fef89`@1145 |
| sec5-sentences | 2 | `721da4c14d11`@1697, `92115dd7edef`@1725 |

- **Over hgreendlinger** (14 rows). These are the rows that name a `TorsionFreeGreendlingerLeaf` form: nm-endpoints
  8, cite-hull 3 (`bcc99703f838`, `2d1cd22e5f49`, `2f997e5af4e6`), cite-hull+kh-ejz+nm-endpoints 2, and
  sec5-sentences `721da4c14d11`.
- **Partial by the lanes' own grades** (3 rows). The union rule keeps a row partial while any lane grades it
  partial.
  - `a9dd4b90e479`: cite-hull, sec5-sentences;
  - `3009704fef89`: cite-ejz, jacobson;
  - `92115dd7edef`: baseline-debt, cite-osin, dgo-analytic, sec5-sentences.

## hull-bridge name flips

hull-bridge maps 27 declarations over the least-area leaves to 21 `_of_greendlinger` forms. The forms are in
`TorsionFreeGreendlingerForms` (99db3338a), `TorsionFreeGreendlingerSentences` and `HullSCGreendlingerForms`
(2aa98f8cc). Each new form binds only hgreendlinger.

- **Baseline at de0c922ef.**
  - Old names: 36 active lines, 27 `buried-conditional` and 9 `open-predicate`.
  - New names: 21 lines, one `buried-conditional` line each. The verifier reports no `open-predicate` finding on the
    new forms.
- **When the old lines retire.** They go stale at the first merge after no row names an old declaration. All 27 old
  declarations are still defined at origin. At 0793191e3, besides hull-bridge's own rows:
  - sec5-sentences rows name 24 of them;
  - cite-hull names `manuscriptSentence_hullCommonQuotient_of_leastAreaLeaves` and
    `HullSC.hullOneStepStatement_of_leastAreaLeaves`;
  - hull-respell names `RelHyp.fournierFacioQuotientStatement_of_leastAreaLeaves`.

## Row files

- 37 row files are on origin.
- Merged so far:
  - the 31 row commits between 5f9c16b7b and 045b5f849, the latest being a7e53cf75 (hull-bridge, the
    `TorsionFreeGreendlingerForms` rows) and 31451e495 (nm-endpoints, the closed hKO names);
  - a032ab802 (dgo-analytic), entered at merge 14.
- Not yet on origin at 0793191e3: hull-bridge's appended rows for tex 1636, 1650, 1675, 284 and 1718, which it has
  announced.

## Next

- Re-merge whenever a lane lands rows, and at least every ~2 h. hull-bridge's appended rows are next.
- systolic-counts: land the verifier fixes. census then re-runs verify-unconditional on MSI and revises the lines
  that quote the hKO false red.
- The hull-bridge flips retire their old lines once the sec5-sentences, cite-hull and hull-respell rows name the
  `_of_greendlinger` forms.
