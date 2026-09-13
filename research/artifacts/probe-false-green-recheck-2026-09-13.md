# Probe green records rechecked after the artifact-restore fix (2026-09-13)

Lane `ex-palomar-hygiene`. This follows `research/artifacts/probe-artifact-restore-empty-log-defect-2026-09-13.md`
(7d41d1a16). That defect lets a module restored from the shared Lake artifact cache print no messages. So a green
record written by the old job template certifies a Palomar module only if its build log shows the module as Built.

**Result.** Every green record of the pc and fz campaigns was checked. Only one gated module was neither Built nor
Replayed and still needed a check: `Palomar/STWProblemXXIIModelTests.lean`, which is on main. It was re-probed once
with the fixed template, and it is clean. Nothing that landed is a false green.

## 1. Template rollout

Each probe script uploads its own remote template. The campaign project directory on MSI is `$P` below.

| probe script | template it uploads | before | after |
|---|---|---|---|
| `fzprobe.sh` (bc and fz campaigns) | `$P/bc/bcjob.template.sh` | e8837d2b… (pre-fix) | 956f7e4d18ebde0f6d2f3fd6b1db7022 |
| `pcprobe.sh` (pc campaign) | `$P/pc/pcjob.template.sh` | e8837d2b… (pre-fix) | 956f7e4d18ebde0f6d2f3fd6b1db7022 |

- **What 956f7e4d is.** It is main's `tools/bc-swarm/remote/bcjob.template.sh` at 7d41d1a16 with only `__MSI_GROUP__` and
  `__MSI_USER__` filled in. That md5 was computed from main's blob and equals pc-infra's `pcjob.template.fixed2.sh`.
- **How it was installed.** Copied to a temporary file in the same directory, md5-checked, then renamed over the
  template with `mv`, at 08:54 CDT. No process had a template open. A rename cannot hand a half-written file to a
  `sed` that is reading the template. The old copies are kept as `*.pre-replay-fix-0913`.
- **nm campaign: not exposed, not reinstalled.** `nmprobe.sh` builds its job locally from its own `remote/job.template.sh`.
  That template has a different layout: a `__CLONE__` placeholder and per-lane clones, so the bc template would not run
  there. It does restore artifacts, but:
  - it accepts only `GroupApproximation/**/*.lean` overlays;
  - that library builds with `-DwarningAsError=true`, so an incomplete proof fails the build and never enters the cache;
  - it has no closure-count gate.
- **lixs campaign.** No probe script or job template exists: the MSI `lixs/remote` holds only a clone script.

## 2. Why only Palomar modules can be false greens

Under the old template:
- **Axiom drivers.** Every `#print axioms` line of the overlay must come back as a closure (rc=7). A restored driver
  prints none, so it makes a probe fail, not pass.
- **`GroupApproximation` modules.** An incomplete proof is an error, so no successful build of such bytes exists to
  restore.
- **Palomar modules outside `*Challenge.lean`.** They build without `warningAsError`, so the hole gate reads a warning. A
  restored module prints no warning. These are the only false-green candidates.

## 3. Inventory

- **Records.** All 76 `*.green.*` records in the pc (14) and fz (62) lane directories. The bc campaign directory holds
  no green records, and the lixs campaign has none either. pc-infra's calibration record `.calib-falsegreen.` is
  excluded by name.
- **Gated paths.** 347 in total:
  - every `Palomar/*.lean` outside `*Challenge.lean` that a record lists as compiled;
  - every file whose `#print axioms` closures appear in that probe's build log.
- **Test.** Look for an exact `Built <Module>` or `Replayed <Module>` token in the retained build log of that probe.
  The script and its data are in the lane's MSI directory `ex/ex-palomar-hygiene/`.
- **Result.** 345 paths were Built or Replayed. Two were neither:

| probe | lane | path | verdict |
|---|---|---|---|
| 0913-082532-24859 | pc-infra | `GroupApproximation/Pestov91/ProbeSmoke.lean` | calibration run with the fixed template; `[job] replay:` elaborated it; correct; not on main |
| 0913-054608-34854 | x22-palomar | `Palomar/STWProblemXXIIModelTests.lean`, md5 92cc422a… | landed at 8444aeb6c and current on main; in no Comparator config (library `PalomarSTWProblemXXIIModelTests`); needed a re-probe |

Among the 22 records that overlay Palomar modules other than challenges, every Solution, driver and bridge module was
Built.

## 4. Re-probe of the one pending module

- **Probe.** 0913-091934-38820, lane `ex-palomar-hygiene`, fixed template, base 6ef1f43fa. The overlay was main's bytes of
  `Palomar/STWProblemXXIIModelTests.lean` (md5 92cc422a27918e262d6222b31933f13a), module
  `Palomar.STWProblemXXIIModelTests`.
- **Log.** The module was not Built, and `[job] replay:` elaborated it with `lake env lean`. The only incomplete-proof
  warnings in the log are the challenge's deliberate holes, `Palomar/STWProblemXXIIChallenge.lean:162:8` and `:175:8`.
  The replayed module adds none.
- **Verdict.** PROBE GREEN, record `ex-palomar-hygiene.green.0913-091934-38820`. Main's file also contains no hole
  token.

## 5. Submitted configurations and their Comparator runs

The latest successful `Palomar comparator` run per configuration. A run rejects any axiom outside the permitted list,
`sorryAx` included.

| configuration | run | head | notes |
|---|---|---|---|
| `comparator-pestov91.json` | 34751904895 | e32bac3f3 | after it, 7bbaa02ac and ce417f2d3 changed only comments and docstrings of the Challenge and Solution (the code lines with comments removed are identical); palomar-check green at ce417f2d3 (34761988439) |
| `comparator-type-a2.json` | 34751922211 | e32bac3f3 | |
| `comparator-guba-thompson.json` | 34752278083 | 4be3a3a5c | |
| `comparator-gkp-commuting-actions.json` | 34752484282 | d18407e34 | |
| `comparator-stw-x1.json` | 34752696134 | d18407e34 | |
| `comparator-blanchard-toeplitz.json` | 34758065578 | 114eeb244 | |
| `comparator-stw-xxii.json` | 34759962400 | 7d41d1a16 | 34758151828 on 114eeb244 failed |
| `comparator-lix.json` | 34758480260 | 114eeb244 | |
| `comparator-bowen-chapman.json` | 34735545983 | 1d67f09d0 | |

These runs certify the Solution modules and their closures. Model-test and driver modules sit outside every
configuration, so section 3 is their only check.

## 6. Smaller findings (no gate reads them)

- **The per-module summary matches substrings.** It prints REPLAYED from `grep -qF "Replayed $m"`, which also matches
  `Replayed <m>Axioms`. Probe 0913-054608-34854 therefore printed `REPLAYED Palomar.STWProblemXXIIModelTests`, although
  only `...ModelTestsAxioms` was replayed.
  - No gate is affected: the replay rule matches Built exactly, and the gates read the log.
  - Suggested fix: `grep -qE "Replayed ${m//./\\.}( |\$)"`. It is not installed, so the remote copies stay byte-equal to
    main's template.
- **pc-infra's `pcprobe.sh.new` (02:36) is out of date.** Its header describes the rejected v1 fix, a rebuild with
  artifact restore off. After the install above, the live `pcprobe.sh` header is true again: a byte copy of main's
  template with the placeholders filled in.
- **Roster change.** Lane `ex-palomar-hygiene` was added to the rosters of `pcprobe.sh` and `pcland.sh`, by an atomic
  rename, for this recheck and the Pestov 9.1 docstring landing.
