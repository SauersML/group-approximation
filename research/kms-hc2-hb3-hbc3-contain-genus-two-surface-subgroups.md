---
rg: 2
id: kms-hc2-hb3-hbc3-contain-genus-two-surface-subgroups
kind: claim
title: For every odd prime p, the hyperbolic KMS groups G_HC2(2)(p), G_HB2(3)(p) and G_HBC2(3)(p) contain quasiconvex genus-two surface subgroups
distinct_from:
  kms-hb2-groups-contain-genus-two-surface-subgroups: that covers the family G_HB2(2)(p); this covers three further KMS families, of half girth types (3,4,4) and (4,4,4)
  one-ended-hyperbolic-groups-contain-surface-subgroups: that asks for every one-ended hyperbolic group; this answers it for three infinite families of hyperbolic groups, with property (T) for p >= 7 or p >= 11
artifacts:
  - experiments/kms-hb2-surface-subgroups/search-results/hc2-t24.json
  - experiments/kms-hb2-surface-subgroups/search-results/hb3-t16.json
  - experiments/kms-hb2-surface-subgroups/search-results/hbc3-t16.json
  - experiments/kms-hb2-surface-subgroups/verify_kms_certificates.py
  - experiments/kms-hb2-surface-subgroups/search-results/verify-kms-certificates.log
  - research/artifacts/hl-surface-subgroups-2026-09-14.md
---

**ESTABLISHED (computer-certified).** For every odd prime `p`, each of the following KMS groups of
`cckw-kms-triangle-groups-structure` item 2 contains a quasiconvex subgroup isomorphic to the fundamental group of
the closed orientable surface of genus 2.

| group | half girth type | certificate | chambers | labels |
|---|---|---|---|---|
| `G_HC2(2)(p)` | `(3,4,4)` | `hc2-t24.json`, surface 67 | 24 | `±1, ±2` |
| `G_HB2(3)(p)` | `(4,4,4)` | `hb3-t16.json`, surface 29 | 16 | in `{±1, ±2}` |
| `G_HBC2(3)(p)` | `(4,4,4)` | `hbc3-t16.json`, surface 28 (orientable) | 16 | in `{±1, ±2}` |

With `kms-hb2-groups-contain-genus-two-surface-subgroups`, this covers four of the six hyperbolic KMS families.
- By CCKW Corollary 7.8 (item 5 of `cckw-kms-triangle-groups-structure`), `G_HC2(2)(p)` has property (T) for
  `p ≥ 7`, and `G_HB2(3)(p)`, `G_HBC2(3)(p)` have property (T) for `p ≥ 11`.
- So these are further infinite families of hyperbolic Kazhdan groups with quasiconvex surface subgroups.
- Every finite-index subgroup of each of these groups contains a closed surface group.

Proof: `kms-hc2-hb3-hbc3-contain-genus-two-surface-subgroups-proof`.

**Not covered.**
- `G_HC2(1)(p)`, of type `(3,3,4)`: every orientable girth surface has size at least 48.
- `G_HBC2(2)(p)`, of type `(3,4,4)`.

For both, an exhaustive search of all girth surfaces with `T = 24` found no labelling with labels in
`{±1, ±2}` (`summary-job785007.txt`). Larger label sets and `T = 48` are recorded in the lane artifact.
