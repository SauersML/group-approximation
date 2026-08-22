---
rg: 2
id: conjugated-s3-packets-live-on-n-double-cosets
kind: claim
title: Conjugated S3 correction packets live on outside-normalizer double cosets
distinct_from:
  constant-c3-normalizer-is-f4-leavitt-semilinear: that computes the normalizer group; this computes its action on the proposed kernel correction and shows the entire normalizer gives zero.
  single-conjugated-s3-packet-correction-equation: that excludes changing only one factor; this reduces the parameter space for the surviving two-sided correction.
  rank-five-rectangle-is-one-letter-hecke-element: that absorbs C3 edge coefficients of a hypothetical inverse factor; this uses centrality of a specific three-term S3 kernel relation.
artifacts:
  - research/artifacts/one-nonnormal-packet-corner-correction-2026-08-21.md
---

Let `k` be the sum of the three constant `S_3` transpositions and
`P_x=e[x]k[x^-1]e`.  Then

```text
P_(xn)=P_x                         for n in S_3,
P_(mx)=m P_x m^-1                  for m in N_G(C_3),
P_x=0                              for x in N_G(C_3).
```

The first identity uses centrality of the transposition class sum, the
second invariance of `e` under the normalizer, and the third `eke=0`.
Therefore a nonzero packet parameter is an outside-normalizer class in
`N_G(C_3)\G/S_3`.  Scalar self-similar copies and constant coordinate
changes supply no correction.

