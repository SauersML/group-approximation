---
rg: 2
id: orthogonal-hecke-row-packs-common-source-energy-into-one-root
kind: claim
title: Pack the entire common-source covariance energy into one Steinberg root coefficient
distinct_from:
  gauge-pair-holonomy-needs-one-source-moment: that produces a finite sum of covariance norms; this packages it as one coefficient row.
  affine-leavitt-steinberg-hs-coefficient-decoder: that asks for a full coefficient decoder; this isolates one coefficient.
  rational-unitary-additive-dilation-is-trivial: that rules out additive unitary dilation; this only preserves an existing squared norm with orthogonal matrix units.
---

A fixed finite list of common-source covariance defects `D_j` can be packed
into one matrix coefficient `R=sum_j E_(j1) tensor D_j`, with

```text
m||R||_2^2=sum_j||D_j||_2^2.
```

Thus one Steinberg root can name the entire row.  This reduction does not
prove root-to-coefficient authentication and does not defeat rectangular
escape; it reduces the remaining boundary theorem to one fixed coordinate.
