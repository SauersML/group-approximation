# Root-wire successor report (lane ms-core-5, acting for the lead)

- The other swarm's coordinator stopped at 17:56 on 09-13, and its `root-wire` lane is gone.
- The last wiring wave was wave 16: `lead-wire` c0c1a8e3d at 16:32, 31 modules. The last `root-wire` landing was at 16:08.
- This lane wires the landed modules that queued up after that, with `$NM/nmwire.sh`, one wave at a time.
- Before every wave it checks `landed.log` for root-wire activity and stops if the other swarm resumed.

## Pre-flight

Only `dupcheck.py` survives in `$NM`. root-wire's `rw/rwtool.py`, `rw/rwgate.py` and `rw/rwclosure.py` are not
there, so this lane rebuilt their core in a scratch tool (`rwprep.py`):

- `list <sha>`:
  - finds the unwired landed modules (landed.log paths on the sha, outside the root closure) and their tops;
  - gives each top a verdict: OK, HOLD, NOEVID, DANGLING or LEX.
- `wave <sha> <Module...>`:
  - takes the files the batch makes newly reachable;
  - checks the green gate, holds, dangling imports, cycles inside the new files, a lexical scan and duplicate
    declaration names over the new closure (dupcheck's parser).
- Green gate: a GREEN record in `$NM/lanes` or `fz/lanes` covers a file when either
  - it lists the file with the md5 of its bytes at the sha, or
  - the file lies in the import closure of the record's `# mods` and its blob at the record's base equals its blob at
    the sha.
- Hold:
  - a FAILED record names the file in `# mods` without an md5 line for it, and that record is newer than every
    covering GREEN record; or
  - the file is a roster hold (`OsinLemma94ClassCovers`, red since a25fe2383).
  - Why md5 lines don't count against a file: `nmprobe.sh` writes md5 lines only for overlay files that compiled in
    that build, even when the probe fails. So a FAILED record's md5 line is evidence that the file compiled.
  - The first version held any file named in a FAILED record. That falsely held three wave 17 modules on ct-rank-budget's
    0913-182900-45325, whose errors are all in the new `DynamicRankBudgetReturnTransientIdeal`, while the six rooted
    files it lists match origin's bytes. The rule was corrected at ~18:40.
  - A target that never compiled because its build stopped elsewhere stays held until a newer green record covers it.
    root-wire released some of those by reading the log; this lane does not.
- Duplicate hits whose matching line is docstring prose (`theorem of both modules ...`) are read by hand and ignored.

## State at a188b6cc6 (09-13 ~18:25)

- Root closure: 6530 files.
- Unwired landed modules: 296, with 148 tops. Of the tops, 86 are OK, 24 HOLD and 38 NOEVID.
- LIX lanes (`lix-*`, `rescue-lix`) are held as in-flight campaign files, as in root-wire's hold table.

## Held

| module | reason | owner |
|---|---|---|
| ~~`Manuscript.ChainCore.BilateralThreeClosures`, `Algebra.BilateralThreeCellZOrder`~~ released ~19:05 | reached `Dynamics/BilateralThreeCellClopen`, which redeclared `ClopenCrossedProduct.coeff_injective`; fixed at 131abe1b5, GREEN 0913-185912-77650 | ct-bilateral-cell |
| `Dynamics.ClopenCrossedProductAlgebra` | global `ClopenCoeff.instAlgebra`, a second `Algebra (ZMod 2) R_X` beside ms-units' `zmodTwoAlgebra`; waits for main's ruling | ms-compress-3 |
| `Estimating.OsinLemma94ClassCovers` | red since a25fe2383 (roster) | hull-component |
| `Algebra.IntegerPolynomialUnisolvence` | red: never compiled, application type mismatch at 122:80 (ℤ vs ℂ coefficients); ms-traces-1 probe 0913-185628-64856 | dgo-geometric |
| `Dynamics.CoreKernelFTwo` and its importers (`CoreKernelRelativeElementary`, `InvolutionLocalizationClosed`, ...) | FAILED 0913-182039-93403 newer than GREEN 0913-181305-25708 | ms-units |
| LIX campaign files | in flight | LIX lanes |

## Wave 17 (calibration), launched 09-13 ~18:27

15 ct/ms modules:

- `Dynamics.{TwoEndedMatrixUnits, RankTwoRestrictionImageFinite, ReturnCornerGeneration, ChainCoreTailModels,
  TwoEndedTailModels}`
- `Manuscript.NonMFSentences.{DynamicRankBudgetInducedCore, DynamicRankBudgetReturnKernel,
  DynamicRankBudgetTorsionTransfer, CompressionRadicalClosedEndpoints, CompressionRadicalPrintedObjects,
  KazhdanProjectionOrderSentences, TransportSentencesAxiomAudit, IntroCompressorSentences,
  HeadlineMaximalProperIsometry}`
- `Algebra.LEFRingStablyFinite`

Pre-flight at 172725674:

- 37 newly reachable files (closure 6530 → 6567), every one covered by a GREEN record;
- 0 held, no dangling import, no cycle, 0 lexical hits;
- one duplicate hit, `of`, is docstring prose in `TransportSentencesAxiomAudit`.

`BilateralThreeClosures` was dropped from the first draft, after the `coeff_injective` collision.

- The root build (tag 0913-183036-54182, base 99c14b3fb) went to SLURM job 720944 with 32 CPUs and 160G.
  `dispatch.sh` sends every job of more than 8 CPUs to `msismall,amdsmall`.
- The job sat PENDING with "Nodes required for job are DOWN, DRAINED or reserved", and the estimated start was 19:47.
- At ~18:44 `scontrol update job=720944 partition=msismall,amdsmall,agsmall` added agsmall, which had 2466 idle CPUs on
  mixed nodes. The memory request and nmwire's `sbatch --wait` flow are unchanged.
- The wave 18 draft (30 gate-OK tops, not launched) pre-flights clean together with wave 17 at def464f1b: 86 newly
  reachable files, 0 held, 0 without green evidence.

- Later `scontrol update` calls added `sioux` and shortened the time limit to 1h30m. The job started at 19:08 on acl42
  (sioux, 32 CPUs).

Result: **ROOT GREEN, landed ef5f85c15** (15 import lines after line 5164).
- Build: 15222 jobs; `Built GroupApproximation` took 387s.
- 1 GroupApproximation module was rebuilt and the rest were restored from the artifact cache.

## Evidence and holds, 18:45–19:10

- `coeff_injective` collision fixed by ct-bilateral-cell at 131abe1b5.
  - GREEN record 0913-185912-77650 at abcbd8c9c covers the four bilateral modules.
  - `BilateralThreeClosures` and `BilateralThreeCellZOrder` join the wave 18 draft.
- ms-traces-1 GREEN record 0913-190411-7498 covers seven unevidenced tops: `LaurentMonomialUnits`, `SupportedCodimension`,
  `SurgeryGCellCollapse`, `LeavittKOnePowerColimit`, `LeavittKOneRankTwo`, `DynamicRankBudgetInducedCoreReverse`,
  `AmenableTraceAnswersProblemX`. They join the wave 19 draft.
  - All seven were restored from the artifact cache, and that probe job predates the re-elaboration fix 7d41d1a16.
  - This lane's lexical scan finds no `sorry`/`admit`/`axiom`/`native_decide` in any newly reachable file.
- Tool fix: `covering_green` now returns the newest covering GREEN record under either rule.
  - Before, an older md5 match could shadow a newer transitive cover, so a released module still read as held.
- Joint pre-flight of waves 17–19 at 2f116d20d: 84 modules, closure 6531 → 6701, no hold, no missing evidence, no
  dangling import, no cycle. The only duplicate-name hits are docstring prose (`theorem of both modules`,
  `structure by unfolding`, `class by class`).
