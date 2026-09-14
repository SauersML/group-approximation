# Surjunctive nonsofic group: Palomar submission candidate

**Current status: withdrawn; documentation reviewed.** The coordinates below
are the former submission, not an active submission. The
[September 13 proof and literature audit](surjunctive-nonsofic-literature-review-2026-09-13.md)
supersedes the preliminary bibliography assessment below. It corrects
Arzhantseva–Gal's citation, adds omitted classical credits and earlier
rigidity sources, and clarifies the evidence for the problem's 2010 history.
The first proposer and Lawton's abstract page remain unverified.

Result: there exists a finitely generated surjunctive group that is not sofic.

## Immutable submission coordinates

- Repository: https://github.com/SauersML/group-approximation
- Commit: `6738ce3d092e23a5976f6d45042f4d92c12bf5b0`
- Preparation branch: `palomar/bowen-chapman-ready`
- Comparator configuration: `Palomar/comparator-bowen-chapman.json`
- Metadata: `formalization.yaml` at that commit
- Lean: `leanprover/lean4:v4.32.0`

Use the immutable commit, not the moving `main` branch or the shared local
working tree. The preparation commit changes only the submission README,
metadata, and the metadata selection in the source-check script. Its parent is
`035c3cc48b3c51bd2ace7a7df83a6eb286f3a8c9`; the mathematical proof is unchanged.

The single configuration selects two formulations of the same separation:

1. `BowenChapman.not_all_surjunctive_groups_sofic`
2. `BowenChapman.exists_finitelyGenerated_surjunctive_not_sofic`

Both statements are unconditional. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted. Finite presentation is not claimed.

## Verification

- [Comparator with NanoDa enabled](https://github.com/SauersML/group-approximation/actions/runs/34785942633): **passed**.
- [Submission surface, statement and axiom checks](https://github.com/SauersML/group-approximation/actions/runs/34785945798): **passed**.

Both runs target the exact commit above. The logs explicitly confirm that
NanoDa and Lean's default kernel accept the selected solution. Comparator
accepted it against the challenge at 22:17:24 UTC on September 13, 2026.
The separate statement check confirms identical elaborated statements. Each
selected theorem's complete axiom closure is exactly
`[propext, Classical.choice, Quot.sound]`. The source/metadata gate and its
calibration checks also passed.

Downloaded run logs are in `/tmp/palomar-bowen-chapman-20260913/`, named
`comparator-run.log` and `surface-run.log`. The linked GitHub runs provide
the public verification evidence. Preparation is complete; Palomar intake
was subsequently completed as recorded below.

## Credit and scope

The witness is the symmetric double of the polynomial/Laurent polynomial
pair in [Kun and Thom, Theorems A and E](https://arxiv.org/abs/2608.06222v3).
They supplied the construction and nonsoficity. The new ingredient is the
surjunctivity theorem for symmetric doubles of surjunctive groups, whose proof
is in `research/artifacts/finitary-split-extension-surjunctivity-2026-09-11.md`.
The Lean endpoint is `GroupApproximation.BowenChapman.exists_fg_surjunctive_not_isSofic`.

The question appears as OP-11 in Ceccherini-Silberstein and Coornaert's
*Cellular Automata and Groups* and as Problem 1.1 in
[Bowen and Chapman](https://arxiv.org/abs/2511.06586).
Their invariant-random-subgroup result does not prove the group statement.
The metadata gives the mathematical sources and separately records Astra,
Claude, and Codex's contributions, with human author responsibility.

A bounded literature search on September 13 used, among other queries,
"surjunctive nonsofic group", "surjunctive not sofic double", and
"surjunctive OP-11", together with the primary papers above. It found no
earlier proof of the group separation. This is not an exhaustive priority
certification. No human expert review is claimed.

## Submission status

The user approved the exact repository, commit, configuration, and declaration
as a responsible author or maintainer, and approved the names Sauers/SauersML.
Palomar accepted submission `5ad9mr3alq1c` at 2026-09-13 22:29:05 UTC.
At the user's request it was withdrawn at 2026-09-13 22:41:00 UTC.
The API confirms `status: withdrawn`, `registration_consent: false`, and
`registered_url: null`. No resubmission is authorized. The former official run is
[34786933517](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/34786933517).
The temporary verification tag and secret gist were both deleted after intake.

Private access credentials are outside the repository in the owner-only
directory `/tmp/palomar-bc-intake.WzCOkg`. Do not publish its contents.
Registration was never requested. Palomar requires the user to see the
specific review and approve its publication before registration. See the
[Palomar contribution policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
and [agent submission protocol](https://submit.palomar-registry.org/llms.txt).
