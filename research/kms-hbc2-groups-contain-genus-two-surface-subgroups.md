---
rg: 2
id: kms-hbc2-groups-contain-genus-two-surface-subgroups
kind: claim
title: For p = 5 and every prime p >= 7, the hyperbolic Kazhdan KMS groups G_HBC2(2)(p) contain quasiconvex genus-two surface subgroups
distinct_from:
  kms-hc2-hb3-hbc3-contain-genus-two-surface-subgroups: that covers G_HC2(2), G_HB2(3) and G_HBC2(3) at every odd prime with labels in {±1, ±2}; this covers the fifth family G_HBC2(2), which has no labelling of size 24 with labels in {±1, ±2, ±3}
  kms-hb2-groups-contain-genus-two-surface-subgroups: that covers the family G_HB2(2)(p); this covers G_HBC2(2)(p)
  one-ended-hyperbolic-groups-contain-surface-subgroups: that asks for every one-ended hyperbolic group; this answers it for the family G_HBC2(2)(p), p >= 5, with property (T) for p >= 7
artifacts:
  - experiments/kms-surface-girth-general/certificates/hbc2-integer-t24-n6.json
  - experiments/kms-surface-girth-general/verify-hbc2-integer-t24-n6.log
  - experiments/kms-surface-girth-general/certificates/hbc2-f5-t24.json
  - experiments/kms-surface-girth-general/verify-hbc2-f5-t24.log
  - experiments/kms-surface-girth-general/verify_modp.py
---

**ESTABLISHED (computer-certified).** Let `p = 5` or `p ≥ 7` be prime. The KMS group `G_HBC2(2)(p)` of
`cckw-kms-triangle-groups-structure` item 2 (half girth type `(3,4,4)`) contains a quasiconvex subgroup isomorphic
to the fundamental group of the closed orientable surface of genus 2.

| primes | certificate | surface | chambers | labels |
|---|---|---|---|---|
| every prime `p ≥ 7` | `hbc2-integer-t24-n6.json` | 67 (orientable, `χ = −2`) | 24 | integers in `[−6, 6]`, divisible only by `2, 3, 5` |
| `p = 5` | `hbc2-f5-t24.json` | 67 (orientable, `χ = −2`) | 24 | residues mod 5 |

- By CCKW Corollary 7.8 (item 5 of `cckw-kms-triangle-groups-structure`), `G_HBC2(2)(p)` has property (T) for
  `p ≥ 7`. So this is a further infinite family of hyperbolic Kazhdan groups with quasiconvex surface subgroups, and
  every finite-index subgroup of each of these groups contains a closed surface group.
- With `kms-hb2-groups-contain-genus-two-surface-subgroups` and `kms-hc2-hb3-hbc3-contain-genus-two-surface-subgroups`,
  five of the six hyperbolic KMS families now have surface subgroups for all primes `p ≥ 7`.
- The same certificates also give non-orientable examples: surface 71 of `hbc2-integer-t24-n6.json` and surface 5
  of `hbc2-f5-t24.json` (both `χ = −2`).

Proof: `kms-hbc2-genus-two-surface-subgroups-proof`.

**Why earlier searches missed it.** No girth surface with 24 chambers has a labelling with labels in
`{±1, ±2, ±3}` (`summary-job788598.txt`). On surfaces 65, 67 and 71 there is also none with absolute values in
`{1, 2, 4, 8}` or `{1, 2, 4, 7, 8}`, and on surfaces 65 and 67 none with absolute values in `{1, 2, 4, 8, 16}`
(`logs/int-hbc2-pow2*.log`, `logs/int-hbc2-1247.log`). The integer labellings of surface 67 found with `|x| ≤ 6`, `10`
and `15` all use labels divisible by `3` and by `5`.

**Not covered.** `p = 3`. None of the 72 girth surfaces with 24 chambers has a labelling over `F_3`
(`logs/feas3-hbc2-t24-p3.log`, exhaustive over labels `{1, 2}`); larger surfaces were not searched. This is a search
outcome, not an obstruction.
