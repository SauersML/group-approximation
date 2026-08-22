---
rg: 2
id: canonical-iwahori-one-hecke-overlap-saturates
kind: claim
title: Every canonical liftable Iwahori projection saturates one Hecke compression overlap
distinct_from:
  canonical-iwahori-projection-commutant-transfer: that is stated as simultaneous commutator transfer for the second vertex; this is the one-real-number compression form for each fixed generator.
  single-hecke-average-isometry-for-lambda-central-unitaries: that is a higher-rank convex-average norm equality for subgroup-central unitaries; this is the rank-one projection overlap tau(PUPU*) with no property-T contraction.
---

OPEN.  In the setup of `canonical-iwahori-projection-commutant-transfer`, let
`p_n` have trace and corank bounded below and asymptotically commute with the
first vertex.  For every fixed generator `c` of the second vertex, put
`U_n=pi_(n,-)(c)`.  Then

```text
tr_(d_n)(p_n U_n p_n U_n^*)-tr_(d_n)(p_n) -> 0.              (COH1)
```

Equivalently `||p_n U_n p_n||_2^2` saturates its universal upper bound
`tr(p_n)`.  By `iwahori-projection-overlap-is-a-spherical-coefficient`, this
says that every associated centered spherical coefficient tends to one on
the second-vertex generators.

The scalarized Gao carrier and its orthogonal Hecke tower do not supply
`(COH1)`: their commuting square controls the conditional first moments of
group Hecke words, whereas `(COH1)` is a mixed fourth moment involving an
ambient commutant projection not named by the source inclusion.  The missing
input is precisely a matrix-coordinate theorem forcing this one compression
to saturate.
