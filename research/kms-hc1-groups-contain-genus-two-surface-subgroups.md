---
rg: 2
id: kms-hc1-groups-contain-genus-two-surface-subgroups
kind: claim
title: For every prime p >= 5, the hyperbolic Kazhdan KMS groups G_HC2(1)(p) contain quasiconvex genus-two surface subgroups
distinct_from:
  kms-hbc2-groups-contain-genus-two-surface-subgroups: that covers the family G_HBC2(2)(p) of half girth type (3,4,4) with 24-chamber surfaces; this covers G_HC2(1)(p), of half girth type (3,3,4), with a 48-chamber surface
  kms-hc2-hb3-hbc3-contain-genus-two-surface-subgroups: that covers G_HC2(2), G_HB2(3) and G_HBC2(3); this covers G_HC2(1), which that node lists as not covered
  one-ended-hyperbolic-groups-contain-surface-subgroups: that asks for every one-ended hyperbolic group; this answers it for the family G_HC2(1)(p), p >= 5, with property (T) for p >= 7
artifacts:
  - experiments/kms-surface-girth-general/certificates/hc1-integer-t48-n4.json
  - experiments/kms-surface-girth-general/verify-hc1-integer-t48-n4.log
---

**ESTABLISHED (computer-certified).** Let `p ≥ 5` be prime. The KMS group `G_HC2(1)(p)` of
`cckw-kms-triangle-groups-structure` item 2 (half girth type `(3,3,4)`) contains a quasiconvex subgroup isomorphic
to the fundamental group of the closed orientable surface of genus 2.

| primes | certificate | surface | chambers | labels |
|---|---|---|---|---|
| every prime `p ≥ 5` | `hc1-integer-t48-n4.json` | 190 of 191 (orientable, `χ = −2`) | 48 | integers in `[−4, 4]`, divisible only by `2, 3` |

- By CCKW Corollary 7.8 (item 5 of `cckw-kms-triangle-groups-structure`), `G_HC2(1)(p)` has property (T) for `p ≥ 7`.
  Every finite-index subgroup of each of these groups contains a closed surface group.
- With `kms-hb2-groups-contain-genus-two-surface-subgroups`, `kms-hc2-hb3-hbc3-contain-genus-two-surface-subgroups`
  and `kms-hbc2-groups-contain-genus-two-surface-subgroups`, all six hyperbolic KMS families of CCKW contain
  quasiconvex genus-two surface subgroups for every prime `p ≥ 5`; in particular every hyperbolic KMS group over
  `F_p` with property (T) by CCKW Corollary 7.8 does.

Proof: `kms-hc1-genus-two-surface-subgroups-proof`.

**Why earlier searches missed it.** The girth surfaces of this type with 24 chambers (5, all non-orientable) have
no labelling over `F_7`, and none with integer labels in `[−6, 6]` (`logs/feas-hc1-t24-p7.log`,
`logs/int-hc1-t24-n6.log`). With 48 chambers, none of the 191 girth surfaces has a labelling with labels in
`{±1, ±2}` (`summary-job788598.txt`); surface 190 needs labels `±3` or `±4`.

**Not covered.** `p = 3`. Surface 190 has no labelling over `F_3` (`logs/cert-hc1-p3.log`, exhaustive) and no
integer labelling with absolute values in `{1, 2, 4}` or `{1, 2, 4, 8}` (`logs/int-hc1-t48-pow2*.log`); the other
190 girth surfaces were not searched at `p = 3`. These are search outcomes, not obstructions.
