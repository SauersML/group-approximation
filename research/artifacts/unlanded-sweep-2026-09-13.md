# Where each orphaned 09-12 research draft went

Lane unlanded-sweep, session 01UM7nByUPBRzW6q2CVrVhTz, 2026-09-13 00:10 CDT.

The input was the 58 research paths on the unlanded-sweep list (groups A–E).
These were drafts in the shared checkout that on 2026-09-12 were either
missing from main or different from main.

Each path was re-audited by blob. The disk `git hash-object` was compared
with the blob at the tip and with every historical blob of the path; no
`git diff` or `git status` was used. The final audit is against tip
5e3b2f7eb, and no path changed between the previous full audit (b7dcc5c7f)
and that tip.

The shared-checkout sweep of session 012d8gi98ecepGFPCfLPcKBA did most of the
landing while this lane was auditing, in 8f5bd6faa (09-12 23:18) and
9a95dafb5 (09-12 23:34). This lane's own landings stopped at the land.sh guard
because main already held identical blobs. This lane ran the UGC root merge
independently and got the same bytes (caddc97f9).

| Outcome | Count |
|---|---|
| Landed new at the real path | 29 |
| Merged onto main's text (3-way merge, clean) | 4 |
| Already on main before any sweep | 19 |
| Duplicate or superseded, not landed | 5 |
| Artifact-only (held in attic for the owner) | 1 |
| SKIP-live (mtime within 60 min at audit) | 0 |
| Total | 58 |

No file was judged mathematically wrong. One landed node is truncated and
duplicates an established node (see Flag 1).

## Sessions

| Short | Session |
|---|---|
| 01PWzw | 01PWzwKNBr2dwjX4pucBuXff (group A and fpbs drafts, run 939f35310 → c6c9428bd) |
| 01HaPd2 | 01HaPd2YJDm2EQdhXtMepr2X (UGC drafts, probable) |
| 012d8gi9 | 012d8gi98ecepGFPCfLPcKBA (Gottschalk team; shared-checkout sweep) |
| 018da4ZM | 018da4ZMvDEshSvGp3YdQgZQ |
| 01UM7n | 01UM7nByUPBRzW6q2CVrVhTz (this session; bh-bg lane) |
| 0a930a1d, e26eab2c | short ids, as attributed by the coordinator |
| 01Abcd4f | 01Abcd4fUYaLXqZuLgyTuRf3 |
| 01C2WrMR | 01C2WrMRTVFMVQLpeZGwDc6N |

## Landed new at the real path (29), all by 8f5bd6faa

Paths are under `research/`. The tip blob is at 5e3b2f7eb and equals the disk draft.

| Path | Owner | Tip blob |
|---|---|---|
| fpbs-spectral-margin-survives-product-generator-moves.md | 01PWzw | 389d9cea1 |
| fpbs-spectral-margin-product-move-proof.md | 01PWzw | 6bfe5b2d4 |
| fpbs-large-margin-generating-sets-exist.md | 01PWzw | 605ed4590 |
| fpbs-large-margin-generating-sets-exist-proof.md | 01PWzw | 1d45367a7 |
| fpbs-thom-small-spectral-radius-generating-sets.md | 01PWzw | 7ac03056e |
| fpbs-thom-small-spectral-radius-generating-sets-citation.md | 01PWzw | 13d507b27 |
| artifacts/fpbs/binary-descent-entropy-tail-replay-2026-09-12.json | 01PWzw | 6c68d790f |
| h31-seven-central-image-criterion.md | 01PWzw | 27c8a32e2 |
| h31-seven-central-image-criterion-proof.md | 01PWzw | d71c7db7d |
| h31-finite-quotients-have-no-seven-schur-class.md | 01PWzw | dcc52df9e |
| central-prime-free-hyperbolic-from-h31.md | 01PWzw | ca05bbc10 |
| kms-hc1-reflected-root-word-is-nontrivial.md | 01PWzw | 444c16464 |
| kms-hc1-reflected-root-word-is-nontrivial-proof.md | 01PWzw | 9ccb18400 |
| kms-hc1-finite-images-kill-reflected-root-word.md | 01PWzw | fd62c13f5 |
| non-rf-hyperbolic-via-kms-reflected-root-word.md | 01PWzw | 8568619e7 |
| artifacts/kms-hc1-marked-root-kernel-candidate-2026-09-12.md | 01PWzw | 58595d054 |
| artifacts/hyperbolic-image-compression-kernel-2026-09-12.md | 01PWzw | c779f652f |
| artifacts/hyperbolic-finite-simple-spectrum-construction-2026-09-12.md | 01PWzw | 3319d2712 |
| artifacts/hyperbolic-mf-kazhdan-direct-attack-2026-09-12.md | 01PWzw | 27bf32b04 |
| artifacts/validate-parallel-frontier-2026-09-12.py | 01PWzw | 06fab1a96 |
| artifacts/parallel-frontier-upstream-validation-2026-09-12.json | 01PWzw | 1469b6cf5 |
| finite-density-moments-control-noisy-tails.md | 01HaPd2 | 0f487a8a0 |
| finite-density-moment-tail-proof.md | 01HaPd2 | 8619493ca |
| finite-moment-pairing-2to1-hardness.md | 01HaPd2 | 287aa4fe3 |
| finite-moment-hardness-from-smooth-design.md | 01HaPd2 | 9956bb7ce |
| artifacts/unique-games-finite-density-moments-2026-09-12.md | 01HaPd2 | 866ba4813 |
| artifacts/unique-games-finite-density-moments-replay-2026-09-12.json | 01HaPd2 | 3008c930a |
| artifacts/verify-ugc-finite-density-moments.py | 01HaPd2 | 106d469af |
| nested-finite-subgroup-idempotents-odd-intersection-are-finite.md | 0a930a1d (probable) | d5db587d0 (Flag 1) |

## Merged onto main's text (4)

The base is main's blob from before the disk mtime; ours is the disk text; theirs is the tip.

| Path | Owner | Commit | Base → tip blob | Content kept from the draft |
|---|---|---|---|---|
| fpbs-gap-survives-product-generator-moves.md | 01PWzw (base df535c054, 09-12 17:27) | 8f5bd6faa | c94d39e0f → dfb55fbc0 | pure additions |
| artifacts/rips-central-pullback-finite-image-centers-2026-09-12.md | e26eab2c (base created 23510de00, 09-12 00:35) | 8f5bd6faa | 1d2e3b8da → 9fd3a51fd | pure additions |
| zpc-frozen-equation-menu-has-positive-orbitwise-class.md | unknown (created aed59addc, 08-25) | 8f5bd6faa | 369f3c3d3 → 8e426f118 | one appended bullet |
| unique-games-conjecture.md | 01HaPd2 | 9a95dafb5 | base 659816060, theirs 0bb17bf1a → caddc97f9 | clean merge; this lane's independent merge is byte-identical |

## Already on main before any sweep (19)

| Path | Landed by | Session | Tip blob |
|---|---|---|---|
| artifacts/kl-curvature-redistribution-2026-09-12.md | 43d3818bf | 01PWzw | d975d9c3d |
| kl-length-six-coincidence-saturated-torsion-residue.md | 43d3818bf | 01PWzw | 5dd80ab32 |
| kl-three-equal-residue-shapes-inject-for-every-loop-order.md | 43d3818bf | 01PWzw | 357ccdca9 |
| closed-mcg-asymptotic-host-dichotomy-proof.md | b935df3a5 | 01UM7n | a2d85722c |
| closed-mcg-in-asymptotic-mcg-is-bordered-or-infinite-in-v.md | b935df3a5 | 01UM7n | 769309710 |
| extensions-of-aperiodic-sfts-are-not-residually-finite-actions.md | deea7e068 | 01UM7n | 6486f7cfc |
| extensions-of-aperiodic-sfts-not-rf-proof.md | deea7e068 | 01UM7n | 902095d13 |
| labbe-full-group-lef-via-periodic-relator-shifts.md | deea7e068 | 01UM7n | 7058bb23e |
| labbe-relator-shifts-carry-patch-rich-periodic-points.md | deea7e068 | 01UM7n | f5aa2c6fb |
| zd-full-group-lef-relator-shift-criterion-proof.md | deea7e068 | 01UM7n | ff984ef6a |
| zd-subshift-full-group-lef-via-periodic-relator-shifts.md | deea7e068 | 01UM7n | c8909e50b |
| labbe-shift-derived-full-group-is-lef.md | fd192c1ce | 01UM7n | 90850ac93 |
| artifacts/right-cancellative-pattern-firewall-2026-09-12.md | 520efbfe5 | 012d8gi9 | a9041dad2 |
| cancellative-incidence-patterns-do-not-force-domination.md | 520efbfe5 | 012d8gi9 | f49c71544 |
| artifacts/coset-shift-alphabet-lift-splitting-2026-09-12.md | 8b6539cf9 | 012d8gi9 | 2e009eb1d |
| artifacts/radu-lattice-b2-anchored-gadget-2026-09-12.md | 86e9c2b3e | 012d8gi9 | cbf5f37c6 |
| radu-lattice-radius-two-pairs-force-the-mark-into-the-radical.md | 86e9c2b3e | 012d8gi9 | af26facdb |
| artifacts/hnn-intertwiner-cocycle-on-thompson-v-2026-09-12.md | e8ed69076 (09-12 22:50) | 012d8gi9 | ad01b4e0f |
| almost-automorphism-exponent-pumping-proof.md | a49eed562 (09-12 23:05) | 01UM7n | fd7191b59 |

The draft of the hnn-intertwiner artifact is no longer on disk. The
almost-automorphism route was SKIP-live at first audit, and then its own
bh-bg lane landed it.

## Duplicate or superseded, not landed (5)

| Path | Owner | Disk blob | Main | Why not landed |
|---|---|---|---|---|
| fixed-gottschalk-test-group-is-surjunctive.md | e26eab2c / 018da4ZM | a0cc264d2 | a92dff91c; last 3f71a3a50 (09-12 11:20) | disk is an earlier main blob, missing the permanence paragraph |
| gottschalk-via-matrix-observable-extension.md | 018da4ZM | 54078c78c | ab66e41e0; last 3f71a3a50 | disk is an earlier main blob that 52c49cdda replaced |
| injective-ca-pullbacks-extend-to-matrix-observables.md | 018da4ZM | 93a68dcba | 632af66d9; last f288e7c27 (09-12 11:26) | disk is an earlier main blob |
| formalizable-binary-pairs-over-biorderable-groups-are-affine.md | 0a930a1d | 03f8e9e6e | fac30c3aa; last 6bd8318d3 (09-12 14:04, 018da4ZM) | main's text already contains the draft's paragraph; attic copy in 8f5bd6faa |
| numeric-window-relations-do-not-force-balance-proof.md | 0a930a1d | 5aa2c1730 | 85c9cdf40; last e367b4372 (09-12 16:31, 018da4ZM) | main has the reworded bullet plus a Verification section; attic copy in 8f5bd6faa |

**Group E check.** Main has not edited the three Gottschalk paths since
3f71a3a50 and f288e7c27, and the Gottschalk team (012d8gi9) has made no later
edit. On all three paths main's text is newer than the draft.

## Artifact-only (1)

The draft `ugc-from-finite-moment-pairing-hardness.md` (owner 01HaPd2) is not
at its real path. Its disk text (53730b020) is kept as
`attic/sweep-2026-09-12/research/ugc-from-finite-moment-pairing-hardness.md`,
added by 8f5bd6faa. For why it was held, see Flag 2.

## Cairn check on MSI

**Workspace.** A shared, no-checkout clone of b7dcc5c7f at
/scratch.global/sauer354/cc-sweep13. Setup:

- The 23 swept node ids were marked changed with `git rm --cached`: fpbs ×7,
  h31 ×4, kms ×4, finite-density ×2, finite-moment ×2, nested, zpc,
  almost-automorphism and unique-games-conjecture.
- The UGC root merge result and the held route were copied in as overlays.
- Tooling: python 3.10.9 and `CAIRN_ROOT=<clone> python3 tools/cairn.py`.

**`cairn check --changed`.** changed=47, 0 errors, 18 warnings, EXIT=0. Only
one warning comes from the overlays: the held route creates a claim cycle,
`finite-moment-pairing-2to1-hardness -> smooth-design-rich-2to1-hardness ->
unique-games-conjecture -> finite-moment-pairing-2to1-hardness`.

**`cairn why`, ESTABLISHED with a complete derivation:**

- fpbs-spectral-margin-survives-product-generator-moves (via fpbs-spectral-margin-product-move-proof)
- fpbs-large-margin-generating-sets-exist
- fpbs-thom-small-spectral-radius-generating-sets (citation route)
- h31-seven-central-image-criterion
- kms-hc1-reflected-root-word-is-nontrivial
- finite-density-moments-control-noisy-tails

These are the targets of the four landed routes with `requires: []`:

- h31-seven-central-image-criterion-proof
- kms-hc1-reflected-root-word-is-nontrivial-proof
- finite-density-moment-tail-proof
- fpbs-thom-small-spectral-radius-generating-sets-citation

No status needs to change.

**`cairn why`, OPEN:**

- finite-moment-pairing-2to1-hardness
- nested-finite-subgroup-idempotents-odd-intersection-are-finite ("frontier hole: no live routes")
- zpc-frozen-equation-menu-has-positive-orbitwise-class
- unique-games-conjecture
- hyperbolic-finite-images-exclude-a-central-prime
- non-residually-finite-hyperbolic-group

Of the landed claims, only the nested node has no `## Attempts` section.

## Flags for owners

1. **`nested-finite-subgroup-idempotents-odd-intersection-are-finite.md`**
   (landed by 8f5bd6faa, blob d5db587d0, probable owner 0a930a1d).
   - The body is truncated mid-word at "- every cand".
   - It is an OPEN claim with no route and no `## Attempts`.
   - Its subject duplicates the established
     `nested-idempotents-from-p-regular-intersections-are-equal`
     (w3-vf-linear §12.1).
   - Main touched it within 60 minutes of this sweep, so it was left for its
     owner (SKIP-owner) and this lane did not edit it. The owner should
     retire it or redirect it to the established node.
2. **`ugc-from-finite-moment-pairing-hardness`** (attic, owner 01HaPd2).
   - `cairn why` shows this route does not establish
     `unique-games-conjecture`: it is missing only
     `finite-moment-pairing-2to1-hardness`, which is OPEN.
   - Promoting it would add the claim-cycle warning above.
   - The owner decides whether to promote it.

## Math read

This was a check for gross errors, not a referee report.

- **fpbs.** The bound `|∂F| = d|F| − ⟨A1_F, 1_F⟩ ≥ (d − ||A||)|F|` gives
  `h ≥ d − ||A||`, and one product generator move changes the margin
  `1 + h − ||A||` by at most 2. For the standard generators of F_2, `h = 2`
  and `||A|| = 2√3`, so the margin is `3 − 2√3 < 0`; this is why Thom's
  sets, with the identity removed, are needed.
- **finite-density tails.** Hölder plus hypercontractivity, with
  `T_rho = T_s T_s`.
- **h31 criterion.** The five-term exact sequence plus an averaging
  splitting.

## Non-research paths (list only, none landed)

**Copied to `attic/sweep-2026-09-12/` as `.lean.txt` by 8f5bd6faa (15).**
Each attic blob equals the disk draft, and no disk text was ever on main at
the real path:

| Path (under GroupApproximation/) | mtime 09-12 | State |
|---|---|---|
| CharClass/OddPProductConcat.lean | 12:29 | tracked; main a8deb448d (2391af544, 11:41) is older |
| CharClass/OddPTopPowerAWChain.lean | 12:14 | tracked; main 0f80a4212 (2e8f27ae8, 11:41) is older |
| GroupTheory/HydeLodha/QTwoLemmaFourSixGenerators.lean | 11:08 | tracked; main d01b839ff (3f71a3a50, 018da4ZM) |
| GGT/HullSCLemma51LetterPullbackShortcut.lean | 11:19 | untracked |
| GGT/HullSCLemma51LetterPullbackShortcutArcs.lean | 11:26 | untracked |
| GGT/SystolicDiscZipFold.lean | 10:56 | untracked |
| GGT/SystolicProjectionClique.lean | 10:55 | untracked |
| Kazhdan/GHWCharP.lean | 10:49 | untracked |
| Kazhdan/GHWEntries.lean | 00:47 | untracked |
| Kazhdan/KotowskiOllivierLeaves.lean | 10:53 | untracked |
| Manuscript/NonMF/TorsionFreeKOLeaves.lean | 10:52 | untracked |
| Manuscript/NonMFSentences/KorchaginDirectLimit.lean | 11:10 | untracked |
| Manuscript/NonMFSentences/KorchaginDyadicV.lean | 11:10 | untracked |
| Manuscript/NonMFSentences/KorchaginFullSequenceLiteral.lean | 11:10 | untracked |
| Manuscript/NonMFSentences/KorchaginShiftKernelMF.lean | 11:10 | untracked |

**Not on main and not in attic.** The owner is unknown unless stated:

| Path | mtime | State |
|---|---|---|
| GroupApproximation/BowenChapman/WreathWitnessEndpoint.lean | 09-12 12:10 | never on main |
| GroupApproximation/CharClass/OddPCartanTotal.lean | 09-12 12:28 | never on main |
| GroupApproximation/CharClass/OddPCompare.lean | 09-12 12:22 | never on main |
| GroupApproximation/CharClass/OddPCompB.lean | 09-12 11:29 | never on main |
| GroupApproximation/GroupTheory/HydeLodha/FinitelyPresentedInfiniteSimpleLeaves.lean | 09-12 10:56 | disk text never on main; last main commit 3f71a3a50 (018da4ZM) |
| GroupApproximation/KunThom/SequentialComponentFamilyCompanion.lean | 09-12 15:08 | older main blob; main e7c13785a (09-12 22:40, 01Abcd4f) is newer |
| scripts/PalomarBowenChapmanAxioms.lean | 09-12 11:09 | older main blob; main c1e3df1ef (01C2WrMR) is newer |
| scripts/PalomarBowenChapmanChallengeType.lean | 09-12 11:09 | older main blob; main c1e3df1ef (01C2WrMR) |
| scripts/PalomarBowenChapmanSolutionType.lean | 09-12 11:09 | older main blob; main c1e3df1ef (01C2WrMR) |
| .github/workflows/palomar-check.yml | 09-10 14:49 | older main blob; main c1e3df1ef (01C2WrMR) |
| .github/workflows/palomar-comparator.yml | 09-11 23:57 | older main blob; main c1e3df1ef (01C2WrMR) |

The LIX and CharClass files that the snapshot listed as `M` are byte-identical
to main. Their `M` status is spurious damage to the shared index, and there is
nothing to land.
