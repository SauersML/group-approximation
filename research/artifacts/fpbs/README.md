# Cost-percolation archive (Fixed Price and Benjamini–Schramm), 2026-09-08/09

Provenance: an external research conversation (`6aa09ea0-1018-83ea-b7fb-13119f311a87`,
2026-09-08 18:47 to 2026-09-09 21:57, 55 responses) that was asked to solve the
Fixed Price problem and the Benjamini–Schramm nonuniqueness conjecture. It shipped
18 nested Cairn bundles (responses 1 to 46), 20 standalone documents, replay and
verification scripts, and JSON check/audit records. Everything was wired into this
graph on 2026-09-09 under the `fpbs-` id prefix (`research/fpbs-*.md`).

The archive's own evidence language applies to every node it produced: an
"established" claim records a written deduction or an explicitly imported theorem,
not independent validation. Finite replay scripts check finite assertions only.

## Layout

| path | content |
|---|---|
| `research/artifacts/fpbs/*.md, *.json, *.txt` | the union of the 18 bundles' `research/artifacts/` (143 files: documents as the bundles named them, check and audit JSON, goal-status snapshots) |
| `research/artifacts/fpbs/scripts/` | the bundles' `scripts/replay*.py` plus `verify_reuse_compression.py`, `verify_torsionfree_local.py` |
| `research/artifacts/fpbs/docs/` | the 20 standalone documents exactly as delivered, four scratch notes, `fixed-price-reuse-compression-checks.json`, and `priority-assessment-2026-09-09.md` (the closing priority verdict forwarded by the user) |
| `research/artifacts/fpbs/responses/` | the 55 responses (`NN_MMDD-HHMMSS.md`), `ARCHIVE_README.md` (the archive's own index with one-line openers), `ALL_RESPONSES.md` |
| `notes/fpbs-cost-percolation-2026-09-09/` | `FULL_TRANSCRIPT.md` (prompts, reasoning, tool calls) and `REASONING_AND_RESPONSES.md`; noncanonical, searchable, never cited by nodes |

## Bundles, documents, responses

| bundle (response that shipped it) | standalone document | node families |
|---|---|---|
| percolation (1), continuation (2–3), explored / exploration-cairn (3) | `fixed-price-percolation-research.md`, `fixed-price-percolation-continuation.md` | `fpbs-quantitative-*`, `fpbs-cost-one-*`, `fpbs-reciprocal-*`, `fpbs-wired-*`, `fpbs-attained-*`, `fpbs-non-fixed-price-one-*`, `fpbs-threshold-*` |
| creative (4) | (pivotal / cluster-projection ideas) | `fpbs-pivotal-*`, `fpbs-critical-*`, `fpbs-dyadic-*`, `fpbs-kazhdan-*`, `fpbs-long-*`, `fpbs-sparse-*`, `fpbs-well-*` |
| exploration (8) | `pivotal-exploration.md`, `fixed-price-percolation-exploration.md` | `fpbs-cactus-*`, `fpbs-hierarchical-*`, `fpbs-integrated-*`, `fpbs-regular-*`, `fpbs-bridgeless-*` |
| spectral-spike (9) | `fixed-price-percolation-spectral-spike.md` | `fpbs-collapse-*`, `fpbs-fiid-*`, `fpbs-transitive-*`, `fpbs-uniqueness-*` |
| torsion (10) | `fixed-price-percolation-torsion-actions.md` | `fpbs-aw-*`, `fpbs-torsion-*`, `fpbs-normalized-*`, `fpbs-burnside-*` |
| bounded-exponent (14) | `fixed-price-bounded-exponent-progress.md` | `fpbs-bounded-*`, `fpbs-centralizer-*`, `fpbs-even-*`, `fpbs-first-*`, `fpbs-held-*`, `fpbs-large-*`, `fpbs-finite-*` |
| two-generator (15) | `fixed-price-two-generator-complete-proof.md`, `amen2-complete-proof.md` | `fpbs-two-*`, `fpbs-same-*`, `fpbs-amen2-*`, `fpbs-binary-*`, `fpbs-suchkova-*`, `fpbs-unbounded-*`, `fpbs-positive-*` |
| phase-repair (22) | `fixed-price-phase-repair.md` | `fpbs-arbitrary-*`, `fpbs-average-*`, `fpbs-small-*` |
| connector-capacity (26) | `fixed-price-connector-capacity.md` | `fpbs-cap-*` |
| cut-repair (30) | `fixed-price-cut-repair.md` | `fpbs-cut-*` |
| burnside-explicit (34) | `fixed-price-burnside-explicit-bound.md` | `fpbs-qb-*` |
| small-cancellation (38) | `fixed-price-small-cancellation-family.md` | `fpbs-sc-*` |
| finite-priority (42) | `fixed-price-finite-priority.md` | `fpbs-priority-*` |
| torsionfree-local (46) | `fixed-price-torsionfree-local.md`, `fixed-price-local-sparsifiers.md` | `fpbs-tfl-*`, `fpbs-local-*`, `fpbs-prime-*`, `fpbs-rank-*`, `fpbs-uniformly-*`, `fpbs-action-*`, `fpbs-all-*`, `fpbs-cycle-*`, `fpbs-expansion-*`, `fpbs-logarithmic-*`, `fpbs-short-*` |
| none (47–55) | `fixed-price-conditional-traffic.md`, `fixed-price-reuse-compression.md`, `fixed-price-reuse-localization.md` | authored during the 2026-09-09 integration (see nodes citing those documents) |

## Goals

`fpbs-fixed-price-universal` and `fpbs-benjamini-schramm-universal` are the two
program goals of this region (`root: true`, `goal: true`). The forwarded priority
verdict of 2026-09-09 makes Benjamini–Schramm the primary target for a full
affirmative solution and Fixed Price the target for class-level progress; see
`docs/priority-assessment-2026-09-09.md` and the dated decision notes on the goal
nodes.
