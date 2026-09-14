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
| `Manuscript.SimpleKazhdanSofic.InfiniteSimpleICC` (and `Analysis.GroupVonNeumannIIOneFactor`, reached only through it) | red at origin: FAILED 0913-212821-73088 names it in `# mods` without an md5 line (rewrite found no occurrence at 50:6, type mismatch at 51:8, `sorry` in two printed endpoints) | oa-mcduff |
| `Estimating.OsinLemma94ClassTransitions` | redeclares `OsinLemma94RealizedPolygons.cuttingSides` (l.68), identical to `Estimating/OsinLemma94CuttingSides.lean:48` (w1-binder-1, 3d2744463); fix: import `OsinLemma94CuttingSides` and delete the local def | sec5-sentences (ec3c531fc) |
| ~~`Algebra.IntegerPolynomialUnisolvence`~~ released ~20:00 | was red at 122:80 (ℤ vs ℂ coefficients); fixed by ms-traces-1 at ad637cf5a, GREEN 0913-194043-12780 (BUILT fresh), md5 = origin 77ac966c5 | dgo-geometric → ms-traces-1 |
| ~~`Dynamics.CoreKernelFTwo` and its importers~~ released ~20:00 | FAILED 0913-182039-93403 is ms-units' probe of `TransientTowerFamily`, where `CoreKernelFTwo` compiled; fresh GREEN 0913-194625-49937 covers `CoreKernelFTwo`, `InvolutionLocalizationClosed`, `TransientIdealLocallyMatricial`, `CoreKernelRelativeElementary`, md5 = origin 77ac966c5 | ms-units |
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

## Wave 18, launched 09-13 ~19:42

36 modules:
- the 30 gate-OK tops drafted at 18:30;
- `BilateralThreeClosures` and `BilateralThreeCellZOrder`, released after 131abe1b5 / GREEN 0913-185912-77650;
- the four unwired tops whose closure reaches `Dynamics.ClopenCrossedProductAlgebra`: `Dynamics.RankTwoKazhdanLimitClosed`,
  `Manuscript.NonMFSentences.DynamicRankBudgetAssembly`, `Manuscript.ChainCore.CoreMFRadical` and
  `Manuscript.NonMFSentences.TransientMatrices`.

Main's 19:3x ruling on the instance:
- Wire `ClopenCoeff.instAlgebra` together with all of its importers, so that any diamond against ms-units'
  `zmodTwoAlgebra` shows up in one build.
- `zmodTwoAlgebra` is an `abbrev`, and Mathlib has `Subsingleton (Algebra (ZMod p) R)`.
- A red call site is reported to its lane, which fixes it with `Subsingleton.elim` there.

Pre-flight at 4a92cb8f2:
- 101 newly reachable files (closure 6568 → 6669), all covered by GREEN records;
- 0 held, no dangling import, no cycle, 0 lexical hits;
- one duplicate hit, `by`, is docstring prose (`structure by unfolding`, `class by class`).

Launch:
- The first launcher at ~19:25 stopped before building, after a clean pre-flight. Its guard used `grep -v -q` on
  empty input, which returns 0 under macOS grep. The guard now counts blocking lines with awk.
- Root build tag 0913-194206-22587, base f416195ba. SLURM job 727457 started at once on msismall (acn91).

Deviation from main's 19:3x ruling 2 ("hold `CoreKernelFTwo`'s importers until ms-traces-1's tag"):
- Wave 18's closure newly reaches `CoreKernelFTwo`, `InvolutionLocalizationClosed`, `TransientIdealLocallyMatricial`,
  `CoreKernelRelativeElementary`, `TransientCellsClosed` and `BilateralThreeCoreModels`, through `CoreMFRadical`,
  `DynamicRankBudgetAssembly` and `TransientMatrices`.
- The launch at 19:42 came before the tag. The corrected hold rule no longer counted ms-units' FAILED 0913-182039-93403
  against `CoreKernelFTwo`, which compiled in that build, so the pre-flight passed. I did not cross-check the ruling.
- The tag has since arrived: GREEN 0913-194625-49937 (base 713164f6f) and 0913-194904-64372 (base e4fdd46a2) cover all
  six files, and every md5 line equals origin 77ac966c5. The bytes wave 18 builds are the covered bytes.

Result: **ROOT GREEN, landed lead-wire 6425614c8** at 20:02.
- 36 import lines after line 5179, matching `rw-wave18.mods` exactly.
- Root build: 0 errors, job 727457 on acn91.
- No instance diamond surfaced in the `ClopenCrossedProductAlgebra` chain.
- The lane's own turn was cut by the ~20:03 API outage, after the root landed and before this report and main's
  message; both were written at 20:22.

## Wave 19, launched 09-13 ~20:40

Attempts:
1. 20:25: stopped at the gate. The only blocking line was `OsinLemma94RealizedPolygons.cuttingSides`, declared in both
   `Estimating/OsinLemma94ClassTransitions` (sec5-sentences, ec3c531fc) and `Estimating/OsinLemma94CuttingSides`
   (w1-binder-1, 3d2744463). `ClassTransitions` is dropped and held (see Held); the fix recipe went to main.
2. 20:31: gate clean at 6f63d0e37 (33 modules), but `nmwire.sh` exited rc=255 right after "submitting to SLURM".
   - The MSI SSH master was absent, with another auth attempt in progress.
   - The submitted job 731738 kept running with nothing to land its result, so it was cancelled at ~20:36 after 3:49.
   - `rw-wave19.mods` from that attempt is kept as `rw-wave19.mods.infra-rc255-2031`.
3. ~20:40: launched from `wave19-draft7.mods` (38 modules) with main's 20:3x additions: `CoreModelsLEFClosed`
   (ms-core-2, b7e521e57; 26 census rows wait on it), `DynamicRankBudgetInducedCoreClosed`, `MainAssembly`,
   `OsinGreendlingerWaistV4` / `TorsionFreeResidualsV4`, and `OsinGreendlingerWaistV4Split`.
   - The launcher keeps unwired tops only. `CoreModelsLEFClosed` and `ClassPairTransfer` are not tops; the first is
     reached through `ChainCoreClosures` and `ChainCoreModelsStatement`, and `WaistV4` through `WaistV4Split` and
     `TorsionFreeResidualsV4`.
   - A simulation of the filter at 53963b72a confirmed that all six requested modules are reached.
   - Joint pre-flight at 22ec98b46: 104 newly reachable files (closure 6669 → 6773), 0 blocking lines, 0 lexical hits.
   - Launcher gate at d1b8ef2d9: 36 modules kept, same numbers.

Result: **ROOT GREEN, landed lead-wire a1f1820bd** at 21:17.
- 36 import lines after line 5215, matching `rw-wave19.mods` exactly. Root build tag 0913-204150-7770, base 705832afc.
- At 2fc90db55 all six requested modules are root-reachable.
- This lane's turn ended at the session limit before this report and main's message were written; both were written at
  21:25.

## Wave 20, launched 09-13 ~21:30

- Drafted from the unwired-top listing at 4c84d3cef, the tip after wave 19: 97 tops, 59 OK, 35 NOEVID, 2 HOLD, 1 LEX.
  The draft is the first 36 OK tops.
- The two holds are `OsinLemma94ClassCovers` and `OsinLemma94ClassTransitions`; the second is now in the tool's hold
  list, until ms-compress-1's `cuttingSides` fix.
- The LEX top `OsinLemma94ClassGapHairModel` is a false positive: its hits are docstring prose ("always admit one",
  "Class words admit hairs"). It went past the cap and goes to wave 21.
- New evidence counted in the listing:
  - ms-traces-1 GREEN 0913-203701-58136 (`RingLaurent`, `MinimalSubshiftPeriodicWord`, `TowerMatrixUnits`,
    `BridgeComponentMap`, all restored from the artifact cache);
  - ms-cite-1 GREEN 0913-202623-71495, whose md5 line covers `OsinPocketPinchPosModelsAlgebra`.
- Launcher gate at d20441972: 36 modules kept, 89 newly reachable files (closure 6773 → 6862), 0 blocking lines,
  0 lexical hits.

Result: **ROOT GREEN, landed lead-wire 7d71bbbd1** at 21:53.
- 36 import lines after line 5251, matching `rw-wave20.mods` exactly.
- Root build tag 0913-213249-30665, base 5cf716b0a, job 736338, 15517 jobs.
- The coordinator restart at ~22:04 killed this lane before the report and main's message; both were written at 23:13.

Holds and tool, 21:35–23:13:
- `OsinLemma94ClassTransitions` is released.
  - ms-compress-1 landed 013a2dc59 at 21:38: the file imports `OsinLemma94CuttingSides` and no longer declares
    `cuttingSides`.
  - GREEN 0913-213117-20108 (base ff0f63e83) lists the file with md5 6595bd27…, equal to origin 8f6ff8d76.
- ms-traces-1 GREEN 0913-212948-96923 covers `SimpleKazhdanSofic.FiniteModelsRing` and
  `VanKampen.BridgeComponentPlanar` (restored from the artifact cache).
- `rwprep.py` duplicate scan now skips lines inside `/- … -/` block comments and `--` line comments, for declarations
  and for `namespace`/`end`.
  - A joint pre-flight of waves 20 and 21 had one false blocking line, `GroupApproximation.GGT.VanKampen.of`. It was
    docstring prose ("class of `y`. -/") in `OsinAppendixEulerTwoGonEulerAssembly` and `OsinLemma94CuttingSides`.
  - The launcher's name exception for top-level `of`/`by` covered only non-namespaced prose.

## Wave 21, launched 09-13 ~23:19

- Drafted from the listing at 0a77fefe9, the tip after wave 20: 70 tops, 33 OK, 35 NOEVID (LIX campaign files and the
  held `InfiniteSimpleICC`), 1 HOLD (`ClassCovers`), 1 LEX.
- The draft is `OsinLemma94ClassTransitions` (released), `OsinLemma94ClassGapHairModel` (its lexical hits are docstring
  prose, "admit"), `FiniteModelsRing`, `BridgeComponentPlanar` and the OK tops: 34 modules.
- Launcher gate at 96f7db6f6:
  - 32 kept; `ClosedWalkIslandModel` and `OsinPocketCellWalkOrder` were dropped as no longer unwired tops;
  - 59 newly reachable files (closure 6862 → 6921), 0 blocking lines;
  - the one lexical hit is `ClassGapHairModel`'s prose, read by hand.
- Root build tag 0913-231916-98260, base c57c5e178.
- The two dropped modules are imported only by modules that landed at 23:17, after the listing:
  - `ClosedWalkIslandModel` by `OsinUnboundSameCellPocketModel` (ms-compress-2, 96f7db6f6);
  - `OsinPocketCellWalkOrder` by `OsinGreendlingerWaistV4Euler` (ct-rank-two-limit, 236898aed), whose unwired top is
    `TorsionFreeResidualsV4Euler`.
  Both tops are gate-OK and go into wave 22.
- Wave 22 draft, 7 modules: `TorsionFreeResidualsV4Euler`, `OsinUnboundSameCellPocketModel`,
  `ChainCoreItineraryClosed`, `CoreRingReflectionProofClosed`, `OsinPocketCellCopyClean`,
  `OsinPocketPinchFirstTurnAssembly`, `OsinLemma94SameCellRCellEnclosed`. A joint pre-flight with wave 21 at 36b7126a2
  is clean: 71 newly reachable files (closure 6862 → 6933), 0 blocking lines. It launches after wave 21 lands.
- Queue: job 744525 sat PENDING on `msismall,amdsmall`.
  - The background waiter used since wave 19 never widened anything: it waited for nmwire's "[dispatch] submitting"
    line, which `nmwire.sh` prints only after the build ends.
  - Waves 19 and 20 were scheduled without widening.
  - At ~23:40 the job was widened directly with `scontrol update … partition=msismall,amdsmall,agsmall,sioux`.
  - From wave 22 on, `widen-by-tag.sh` polls `squeue` for the job by tag and widens it while pending.

Result: **ROOT GREEN, landed lead-wire daa821b00** at 23:41.
- 32 import lines after line 5287, matching `rw-wave21.mods` exactly.
- Build: acl42, 15576 jobs, 2 GroupApproximation modules rebuilt.
- Waves 17–21 have wired 155 modules.

## Wave 22, attempted 09-13 23:50 – 09-14 00:05

- Draft from the listing at b3556e93e, the tip after wave 21: 52 tops, 17 OK, 34 NOEVID, 1 HOLD. The draft is all 17
  OK tops, including the 7 drafted at 23:30.
- The launcher stopped at its first step: `git fetch` failed with "Could not resolve host: github.com".
  - Nothing was recorded (`rw-wave22.mods` absent) and nothing was dispatched.
- A relaunch retried the fetch every 30 s, starting 23:59.
- Diagnosis at ~00:01: a local network or DNS outage on the lead machine.
  - The resolver at 127.0.2.2 / 127.0.2.3 returns nothing for `github.com` or `login.msi.umn.edu`, while cached names
    (`api.github.com`, `google.com`) still resolve.
  - `curl https://github.com` fails at once, and the MSI SSH master socket is gone.
  - Reported to main as a blocker. This lane changes no DNS, VPN or system setting and starts no MSI auth.
- This section was written during the outage and lands once pushes work again.
- 00:02:51: the fetch recovered.
  - Launcher gate at b55f73c7a: 15 of 17 kept (`OsinLemma94SameCellRCellEnclosed` and
    `OsinEnclosedSubdiagramLoopCutSucc` are no longer unwired tops), 21 newly reachable files (closure 6921 → 6942),
    0 blocking lines.
- 00:03: `nmwire.sh` exited rc=255 right after "submitting to SLURM" (tag 0914-000329-49958); the MSI hop dropped.
  - The submitted job 749262 was PENDING, and `widen-by-tag.sh` widened it at 00:03:46.
  - The SSH master socket then disappeared (~00:07). One successful query at 00:14 no longer listed the job.
  - No root commit landed. `rw-wave22.mods` from this attempt is kept as `rw-wave22.mods.infra-rc255-0003`.
- ~00:19: DNS resolves again (`github.com` HTTPS 200), but the MSI master stays down.
  - A background task polls `ssh -O check` for up to 90 minutes without starting auth.
  - Once the master is up, it checks job 749262, waits if it is live, and relaunches wave 22 behind the full gate.

- 00:38: the MSI master came back.
  - The orphan job 749262 had COMPLETED at acl42 in 5:00, and its rootout reads ROOT GREEN (15597 jobs, base
    881e3a1a5).
  - Nothing landed that root, because `nmwire.sh` had already exited at dispatch.
- 00:58: the relaunch passed the gate again at bb887b17d: 15 modules, 21 newly reachable files, 0 blocking lines.
  - `nmwire.sh`'s own `git fetch` then failed with "Could not resolve host: github.com" (rc=1). DNS was flapping.
  - That attempt's `rw-wave22.mods` is kept as `rw-wave22.mods.nmwire-rc1-0058`.
- 01:00: fetch, DNS and the MSI master all work again. Wave 22 relaunches from a retrying task:
  - it waits for a working fetch and stops if any root commit landed since daa821b00;
  - it goes through the full gate and widens the job by tag;
  - after an infra failure (unresolved host, or rc=255 once its orphan job clears) it retries, up to 3 attempts;
  - it never retries a gate stop or a real red.

- 01:04–01:24: the retrying relaunch needed about 12 fetch attempts before `github.com` resolved.
  - The gate passed at b856912f2: 15 modules, 21 newly reachable files, 0 blocking lines.
  - `nmwire.sh` then exited rc=4 at its pre-check `msi true || msi up || exit 4`; the master was down again.
  - The retry rule did not treat rc=4 as infra, so it stopped. The attempt's `rw-wave22.mods` is kept as
    `rw-wave22.mods.nmwire-rc4-0124`.
- 01:36: `github.com` resolves and fetch works, but `login.msi.umn.edu` does not resolve and the master socket is missing.
  - Two `msi doctor` processes, started outside this lane, are running.
  - Reported to main as a continuing blocker.
- From 01:37 wave 22 waits behind a stability gate:
  - it requires 5 continuous minutes with both hosts resolving, the master up and no `msi up` / `msi doctor` running,
    so `nmwire.sh` never reaches its `msi up` auth path while MSI is under repair;
  - it treats rc 1, 4 and 255 as infra, with at most two retries after a fresh window and a 3-hour cap;
  - it never retries a gate stop or a real red, and stops if a root commit lands since daa821b00.

Result: **never landed**. No root commit landed after daa821b00.
- The stability-gated task's local logs were lost in the 09-14 08:14 reboot.
- The ROOT GREEN build 0914-024246-75334 in the lead clone (base f607305eb) has 0 wired lines: a plain warm-up, not
  wave 22.

## Reboot recovery, 09-14 08:14–09:xx

- The laptop rebooted at 08:14 and `/private/tmp` was wiped: `nmprobe.sh`, `nmland.sh`, `nmwire.sh`, `landed.log`,
  `lanes/*.green.*`, `wire-queue.txt`, the `rw-wave*.mods` files and this lane's scratch tools.
- Main rebuilt the infra from origin's `tools/nm-swarm` at `$NM=…/f907d0cb…/scratchpad/nm`, with an empty
  `landed.log` and wire queue.
- This lane's tools were restored under `$NM/rw/`:
  - `rwprep.py`: holds `OsinLemma94ClassCovers` and `InfiniteSimpleICC` explicitly, because ICC's FAILED record was
    lost. `list --since <date>` takes candidates from origin commits.
  - `launch-wave.sh`: also stops if any root commit landed after the previous root sha.
  - `widen-by-tag.sh`.
- Evidence (`msi-records.py`):
  - 1,647 MSI probe outputs `cc_clones/*/.nm/out-*.txt` gave 1,578 records in `$NM/rw/msi-records/` (65 without a
    base line, 4 without a verdict).
  - The records carry no md5 lines, because the outputs do not record overlay bytes. A record covers a file only when
    its blob at the probe base equals its blob at the tip; a FAILED output holds all of its targets.
- Unwired tops since 09-12 at d5d1b9db7: 123 (20 OK, 4 HOLD, 99 NOEVID).
  - Of the OK tops, 14 are LIX campaign files (held in flight) and one belongs to another campaign.
  - Of the NOEVID tops, 22 are clearly non-MF campaign modules. They were overlays when probed and need fresh probes
    at the tip; the list went to main.

## Wave 22 (after the reboot), launched 09-14 ~09:xx

- 4 nm tops verified from MSI records: `TorsionFreeResidualsV5`, `FinitelyPresentedInfiniteSimpleLeaves`,
  `BridgeComponentValue`, `OsinPocketCellPinchRefutation`.
- Pre-flight at c9b9218d4: 17 newly reachable files (closure 6921 → 6938), 0 blocking lines.
- Launcher gate at c60e39ee8: same numbers. Root build tag 0914-083344-47173 (base 1dacd6442); job 774854 was widened
  at 08:34 and started at 08:35.
- Evidence audit (per-module lines of each newest covering record's MSI output):
  - fresh builds: `FinitelyPresentedInfiniteSimpleLeaves` (quant-collapse 0912-110242-42142),
    `OsinPocketCellPinchRefutation` (lix-h 0913-234315-3209), `TorsionFreeResidualsV5` and `WaistV5` (ct-rank-two-limit
    0914-082738-17083);
  - cache restores only: 11 further files in `TorsionFreeResidualsV5`'s closure, 2 files covered by ms-traces-1's
    0914-083551-61041, and `BridgeComponentValue` (w1-binder-5 0914-083201-34888).
- Main's ruling (A), 09-14 ~08:45: a cache restore counts as wiring evidence for origin-identical files, as in waves
  17–21. A restore is an earlier successful build at the same input hash, with warnings as errors and closed-axiom
  audits. "Only BUILT counts" applies when a lane lands new bytes. The lexical scan of newly reachable files is clean.
- First build (tag 0914-083344-47173, acn30, 15593 jobs): **ROOT GREEN, but not landed**.
  - `nmwire.sh` logged "push race 1–6" and exited 1.
  - Auth was fine: a bash `git push --dry-run` of the tip through the same credential helper returned
    "Everything up-to-date".
  - The cause was contention: `landed.log` showed 8–16 landings a minute (16 in 08:51). Each of the six attempts
    re-ran the full-tree landing `dupcheck.py` between fetch and push, so every push lost its race.
- `nmwire.sh` landing loop patched at ~08:58; backup `nmwire.sh.orig-0914`:
  - 40 attempts with 1–3 s jitter;
  - the landing dupcheck re-runs only when `.lean` files changed since the last check and that check is more than
    60 s old;
  - push stderr is kept in `msgs/push-<tag>.err` and printed with each race;
  - the commit attribution is appended once, before the loop, with the current session.
- Relaunched ~09:00 through the patched tool.
- Wave 23 draft (23 modules):
  - 4 BUILT-fresh tops: `MatricialQuotientsExpanders`, `ClassGapCollapseModel`, `UnboundScaled`,
    `UnboundScaledDecomposition`;
  - N1's 5 restore tops;
  - N3's 8 ours-nm tops (ms-traces-1 0914-084628-8117): `NoncrossingClosedWalkSectorNoninterleaving`,
    `ClosedWalkEnclosedSubdiagramPieces`, `TorsionFreeResidualsV4Euler`, `ChainCoreOpeningSentence`,
    `ChainCoreItineraryClosed`, `CoreRingReflectionProofClosed`, `DynamicRankBudgetInducedCoreSentences`,
    `TransientCompactWanderingCover`;
  - S2's 6 ours-sk tops (0914-085505-41638).
  - Joint pre-flight with wave 22 at f3893f5b7: 47 newly reachable files, 0 blocking lines; the landing `dupcheck.py`
    predicts 0 collisions.
- ~09:10: wave 23 grows to 37 modules with ms-traces-1's later records:
  - N2b 0914-085827-26227: 6 ours-nm tops;
  - S1b 0914-085925-78566: 5 ours-sk tops;
  - L1 0914-090402-30789: `LEFLevelEmbedding`;
  - on their owners' GREEN records: `OsinPocketPinchPosModelsDiagram` (ms-cite-1) and `LamplighterRing` (sk-lef-action).
  - Joint pre-flight with wave 22 at 3647dc289: 69 newly reachable files (closure 6921 → 6990), 0 blocking lines,
    0 predicted landing collisions.
- Open question to main: 24 green tops that no nm report names (O1 0914-085549-6149, O2 0914-085633-39343,
  O3b 0914-090518-95417; Algebra, Analysis, Kazhdan, KOne, `NonMF.FFFSectionTwoConfiguration`,
  `HydeLodha.QTwoFinitePresentationPerfect`). Not wired unless main confirms they are ours.
- `GGT.VanKampen.FaceSetBoundaryGlue` was red on a linter error (unused simp argument at 276:48, O3 FAILED
  0914-085734-83152).
  - ms-traces-1 landed the fix at bf1aeff09. GREEN 0914-090918-32879 (BUILT, md5 = origin) covers it.
  - No nm report names it either, so it joins the open question: 25 tops.
- Relaunch through the patched `nmwire.sh`:
  - gate at 98858d528: 3 of 4 kept; `BridgeComponentValue` is no longer an unwired top, because a newer landed module
    imports it;
  - 16 newly reachable files, 0 blocking lines;
  - root build tag 0914-090403-31245 (base 2d653dd59, acl42, 15592 jobs); job 780826 widened 09:04, running 09:05.

Result: **ROOT GREEN, landed lead-wire 73b555f38** at 09:16.
- 3 import lines after line 5319, matching `rw-wave22.mods` exactly; the first root commit since daa821b00.
- The patched landing loop landed on attempt 3, after 2 non-fast-forward races. The commit carries the current session
  attribution once.

## Ownership ruling and wave 24 draft, 09-14 ~09:15

Main's ruling on the 24 ambiguous green tops:
- ours, from today's lane commits: `Algebra.OrthogonalRepresentationResiduallyFinite`, `Analysis.KirchbergTraceModels`,
  `Kazhdan.KazhdanNearInvariantVector` (oa-kirchberg), `Analysis.VonNeumannTwistedAmplification`,
  `Analysis.HyperlinearTraceVanishingModels` (oa-mcduff), `Analysis.PauliHyperfiniteFactor` (oa-hyperfinite),
  `Manuscript.NonMF.FFFSectionTwoConfiguration`, `GroupTheory.HydeLodha.QTwoFinitePresentationPerfect`;
- wire the 09-12 restore-tree tops, untouched since the restore and so not in flight: the Algebra O1 tops,
  `PurelyInfinite*`, `CStarMaxTensorExact`, `ReducedGroupCStarCongr`, `KOne.*`,
  `GGT.KazhdanHypGQEightFastTraversal`. All 15 were checked: last origin commit 3f71a3a50;
- hold `Analysis.TraciallyCompleteCStarModelTest` (STW XXII campaign, 31da2ecfd), now in `rwprep.py`'s hold list.

Wave 24 draft, 24 modules: the 8 confirmed tops, the 15 restore-tree tops, and `FaceSetBoundaryGlue`. That file was a
restore-tree file with no owner, so ms-traces-1's successor fix at bf1aeff09 makes it ours. It launches after wave 23
lands.
- The joint pre-flight of waves 23 and 24 at 82916080d found a landing hazard: the infra `dupcheck.py`, which
  `nmwire.sh` runs before each push, predicted a collision named `of`.
  - It was docstring prose in `Analysis/CStarMaxTensorExact` ("structure of the *maximal* completion").
  - Unfixed, wave 24 would have built ROOT GREEN and then been REFUSED at landing.
- `dupcheck.py` patched at ~09:25, backup `dupcheck.py.orig-0914`: lines inside `/- … -/` block comments and `--`
  line comments are skipped, as in `rwprep.py`.
  - The patched file was compile-checked and swapped in with an atomic rename, so a landing check by wave 23's
    `nmwire.sh` cannot read a half-written file.
- `BridgeComponentValue`'s unwired importers, `GGT.VanKampen.DiscDiagramOfPlanarRestrict` and
  `Estimating.OsinUnboundSameCellPocketCellFree` (w1-binder-5 BUILT 0914-083201-34888), are gate-OK and join wave 24:
  26 modules.
- Joint pre-flight with wave 23 at fffd77d7e: 84 newly reachable files (closure 6937 → 7021), 0 blocking lines;
  patched landing dupcheck: 0 collisions; `BridgeComponentValue` reached.

## Wave 23, launched 09-14 ~09:17

- 37 ours tops, the draft recorded above in the wave 22 section.
- Launcher gate at a5ff1a05a:
  - 18 of 37 kept. 19 were dropped as no longer unwired tops, because newer landed modules import them. Among them:
    `SimpleKazhdanSofic.{WordProblemDegreeInvariant, LEFLevelEmbedding, LamplighterRing}` and
    `Analysis.GroupVonNeumannUnitaryGroup`.
  - 21 newly reachable files (closure 6937 → 6958), 0 blocking lines.
- Root build tag 0914-091948-40931, base 2ca5ed20b, acl42, 15613 jobs.

Result: **ROOT GREEN, landed lead-wire ab913eba1** at 09:33.
- 18 import lines after line 5322, matching `rw-wave23.mods` exactly.
- The patched landing loop landed on attempt 9, after 8 non-fast-forward races.
- Waves 17–23 have wired 161 modules.
- The dropped modules are traced to their unwired importer tops for wave 24.

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
