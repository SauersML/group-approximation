# Rescue of uncommitted shared-checkout work, 2026-09-12

User order (2026-09-12 ~22:20 CDT, verbatim): "we must get everything uncommitted into main
carefully, no overwriting or clobber". Lane `ex-rescue` of the EX swarm. It lands only through
`exland.sh` and never writes the shared index or HEAD.

## Scope and method

- Fixed classification tip `T = 83970f525` (2026-09-12 22:45 CDT). Live main was re-read at 23:42
  (`18dddf7c5`), 23:55 (`cfdab43f5`) and 00:05 (`14cc8e071`).
- Candidates are the union of four sets. There are 4948 paths; 4947 exist on disk and one was deleted
  by a local commit.
  - untracked non-ignored files (2960);
  - the index against HEAD (1736 staged);
  - the working tree against the index (272 modified);
  - every path touched by the 18 commits on the checkout's HEAD that are not in main
    (89 paths, merge base `f9431d2b5`).
- Blobs came from `git ls-tree -r`, `git ls-files -s` and `git hash-object --stdin-paths`, without `-w`.
- History came from one `git log --since=2026-07-01 --raw --no-renames` pass over the top-level
  directories, plus a separate pass since 2026-06-01 over the root-level files.
- Each path was re-hashed at least 60 s after its bytes were copied into the lane dir.

## Counts per class

| class | paths | outcome |
|---|---:|---|
| SAME (disk == tip) | 4314 | nothing to do |
| OLDCOPY (disk equals a historical main blob) | 499 | not landed. Includes `formalization.yaml`, `lakefile.toml`, `mf_recognition_complexity.pdf` and `non_mf_groups_exist.pdf`, found by the root-level history pass |
| NEW (absent at T) | 98 | 18 landed by ex-rescue; 35 landed by the parallel sweep; 14 landed by their owners after T; 27 preserved under `attic/sweep-2026-09-12/`; 4 already on main as identical blobs at other paths |
| EDIT-CLEAN (tip == HEAD or index blob) | 1 | `research/zpc-frozen-equation-menu-has-positive-orbitwise-class.md`, landed by the parallel sweep |
| EDIT-MOVED (tip moved, disk not historical) | 35 | 2 landed by the parallel sweep; 1 3-way merged by it; 9 landed by owners after T; 22 preserved under `attic/sweep-2026-09-12/`; 1 already on main as an identical blob |
| DELETED | 2 | nothing deleted from main (see below) |
| Local-commit content absent from main | 5 | 4 snapshotted by ex-rescue; 1 already subsumed |

At 00:05, every NEW, EDIT-CLEAN and EDIT-MOVED path (134) had its disk bytes on main in one of these
forms:
- 79 at their real paths;
- 49 as copies under `attic/sweep-2026-09-12/`;
- 5 as byte-identical blobs at other main paths;
- 1 (`research/unique-games-conjecture.md`) as a clean 3-way merge onto main's newer node.

## Landings

- `e920850a0` (ex-rescue): 18 NEW `notes/nm-swarm/lanes/<lane>.clone` / `nm-endpoints.files` infra
  files. The sweep skipped them, most likely because their one-line contents already exist at sibling
  paths.
- `1ab90e864` (ex-rescue): the four local-commit report versions listed below, as snapshots.
- `8f5bd6faa` 23:18 and `9a95dafb5` 23:34: a parallel sweep answering the same order
  (Claude-Session `012d8gi98ecepGFPCfLPcKBA`).
  - It landed at real paths every node, artifact, note and experiment file ex-rescue had queued. For
    each of those files, the blob it landed is byte-identical to the bytes ex-rescue classified.
  - It preserved the rest under `attic/sweep-2026-09-12/`, renaming `.lean` to `.lean.txt`.
  - ex-rescue re-classified against the live tip before its first push and did not land any path twice.

## Preserved only as copies, with reasons

Under `attic/sweep-2026-09-12/` (by `8f5bd6faa`):
- 17 uncompiled Lean modules, as `.lean.txt`, so no build, orphan scan or wiring job reads them:
  - `CharClass/OddPProductConcat`, `CharClass/OddPTopPowerAWChain`
  - `GGT/HullSCLemma51LetterPullbackShortcut`, `GGT/HullSCLemma51LetterPullbackShortcutArcs`,
    `GGT/SystolicDiscZipFold`, `GGT/SystolicProjectionClique`
  - `GroupTheory/HydeLodha/QTwoLemmaFourSixGenerators`
  - `Kazhdan/GHWCharP`, `Kazhdan/GHWEntries`, `Kazhdan/KotowskiOllivierLeaves`
  - `Manuscript/NonMF/TorsionFreeKOLeaves`
  - `Manuscript/NonMFSentences/KorchaginDirectLimit`, `KorchaginDyadicV`,
    `KorchaginFullSequenceLiteral`, `KorchaginShiftKernelMF`
  - `wip/bowen-chapman/.../KunThom/FixedPointNormalizationBisection`,
    `FixedPointNormalizationComparison`
- `research/formalizable-binary-pairs-over-biorderable-groups-are-affine.md` and
  `research/numeric-window-relations-do-not-force-balance-proof.md`. Both disk edits (14:02, 16:12)
  conflict in a 3-way merge against main's later versions (14:04, 16:31; base = the index blob).
- `research/ugc-from-finite-moment-pairing-hardness.md`, a route into `unique-games-conjecture`, held
  by the sweep so that unreviewed work cannot bear on the UGC root. Its premise
  `finite-moment-pairing-2to1-hardness` is OPEN on main, so the route would not fire. Its owner can
  promote it.
- `README.md`, a clean merge adding a "Group property atlas" section that was never on main
  (`git log -S group-atlas`). The sweep chose the attic.
- `metadata/nm-census-rows/hull-count94.tsv` and `lix-descent.tsv` (census rows).
- 26 non-MF swarm infra files:
  - `notes/nm-swarm/landed.log` and `wire-queue.txt`, where main's blob is a subsequence of disk
    (+58 and +25 lines);
  - 22 lane `.files` lists;
  - `notes/nm-swarm/reports/leavitt-ge.md`;
  - `tools/nm-swarm/nmwire.sh`, which adds dupcheck collision predictions;
  - `tools/nm-swarm/remote/wirejob.template.sh`, which resets the clone root.

Under `wip/uncommitted-2026-09-12/` (by `1ab90e864`), with the `.snapshot` suffix because
`scripts/check.py` walks every `*.lean` under the repository root:
- `notes/lix-stronger-lane-reports/sp-design.md.snapshot`, `sp-powers.md.snapshot`,
  `sp-steenrod.md.snapshot` and `sp-tower.md.snapshot`.
  - These are the versions from local commit `1e21d1365` (2026-09-10 11:40, "Stronger LIX program:
    design report ...").
  - None of these blobs is in main's history under any path. They carry 12, 38, 20 and 13 lines that
    main's versions lack.
  - Main rewrote the reports afterwards, and all four merges (base `f9431d2b5`) conflict, so main's
    reports are untouched.
  - `notes/lix-lane-reports/FLEET_TRAPS.md` from the same commit was not snapshotted, because every
    one of its lines is already in main's version.

Not landed anywhere, because the identical blob is already on main:
- `GroupApproximation/BowenChapman/WreathWitnessEndpoint.lean`, equal to
  `wip/bowen-chapman/GroupApproximation/BowenChapman/WreathWitnessEndpoint.lean`;
- `CharClass/OddPCartanTotal.lean`, `OddPCompare.lean` and `OddPCompB.lean`, equal to
  `attic/inflight/lx-cartan-b/...lean.txt`;
- `GroupTheory/HydeLodha/FinitelyPresentedInfiniteSimpleLeaves.lean`, equal to
  `attic/inflight/hl-lemma46b/...lean.txt`.

Deletions never propagated to main:
- `tools/test_cairn_site.js` was deleted by a local commit, but main and the disk both still hold it.
- `research/quadratic-fiber-weights-and-tail-sentinels-control-prefix-recodings.md` was deleted by a
  local commit and is already absent from main.

## Local commits on the checkout's HEAD

Of the 89 paths they touch:
- 64 carry main's current blob;
- 18 carry blobs from main's history, including `formalization.yaml`, `k1_injectivity_counterexample.tex`
  and both PDFs, found by the root-level pass;
- 2 are the deletions above;
- 5 are the report versions above.

The 17 fpbs Benjamini–Schramm commits of 2026-09-10 are fully on main under other SHAs.

## Live peers seen mid-edit

ex-rescue held these paths because they were modified between 22:38 and 22:55 or changed between two
hashes at 22:48 and 23:02:
- the Labbé / Z^d LEF family and `extensions-of-aperiodic-sfts-*`;
- `coset-shifts-split-off-full-shifts-at-lifted-alphabets` and its artifact;
- `separated-finite-stabilizers-give-modular-hecke-hopficity`;
- `almost-automorphism-exponent-pumping-proof`;
- `char-zero-linear-groups-satisfy-boone-higman` and
  `baumslag-char-zero-metabelian-group-satisfies-boone-higman`;
- `research/artifacts/or-unpeelable-census-scripts-2026-09-12/`;
- `fpbs-normal-subgroup-bounded-cost-fixed-price-one` and `artifacts/fpbs/docs/normal-subgroup-fixed-price.md`;
- `support-pair-unit-scheme-is-finite-over-z`.

By 00:05, each disk copy was on main at its real path, landed by its owner.

## Owner hints (from commit trailers and lane records)

- `fpbs-spectral-margin-*`, `fpbs-large-margin-*`, `fpbs-thom-small-spectral-radius-*`, the KL residue
  nodes and the Boone–Higman char-zero nodes: Claude-Session `01PWzwKNBr2dwjX4pucBuXff`. It landed the
  companion artifact `fpbs-single-product-move-2026-09-12.md` in `04acd6e6a`, the KL residue work in
  `43d3818bf`, and `bh-baumslag-char0-metabelian` in `c33366434`.
- The binary formalizability hub, the numeric window no-go and the nested idempotents: Claude-Session
  `018da4ZMvDEshSvGp3YdQgZQ` (`3170c0b61`, `832009a61`, `2cbbbe196`).
- The Labbé LEF family: Claude-Session `01UM7nByUPBRzW6q2CVrVhTz` (artifact `labbe-lef-2026-09-12.md`, `4d9a53eab`).
- `unique-games-conjecture`: lane `ex-ugc` (`edb8c69cc` and later).
- The UGC finite-density family, the H31 central-image and KMS-HC1 reflected-root families, the three
  `hyperbolic-*` attack artifacts, the parallel-frontier validation and the two Gottschalk notes: no
  trailer. They were written 2026-09-12 00:38–00:51, before the `becc912bd` deletion and restore.
- `notes/nm-swarm/**` and `tools/nm-swarm/**`: the non-MF verbatim swarm, written up to 10:54.
- The four `sp-*.md` snapshots: local commit `1e21d1365`, Claude-Session `01FTzaFhYvdZUXbZ6KpBp6kQ`
  (Co-Authored-By Claude Fable 5.1). The other 17 local commits carry no session trailer.

## Corrections made during the run

- The first history pass omitted root-level paths. That had put `formalization.yaml`, `lakefile.toml`,
  the two PDFs and the local-commit `k1_injectivity_counterexample.tex` in EDIT-MOVED or
  local-commit-absent. The root pass shows they are in main's history, so none of them was
  snapshotted.
- `research/unique-games-conjecture.md`: the disk copy is the classified 00:43 edit and did not change.
  Main holds the parallel sweep's merge of it.

The full table (path, class, disk blob, tip blob, action, landed sha; 4954 rows) is in the lane dir
`ex/lanes/ex-rescue/classification.tsv`, not on main.
