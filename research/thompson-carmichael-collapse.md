---
rg: 2
id: thompson-carmichael-collapse
kind: claim
title: An unbounded Carmichael family of conjugates forces its matrix three-cycle to collapse
artifacts:
  - research/artifacts/thompson-v-r5-coherent-alternating-packet-2026-08-21.md
distinct_from:
  thompson-v-r5-coherent-carmichael-family: that is the open group-theoretic compiler; this is the completed compact-packing argument after the family has been supplied.
  thompson-v-r5-cap-implies-one-word-collapse: that uses a full approximate finite-group table, Gowers--Hatami, flexible enlargement, and alternating-group representation degree; this uses only pair relators and compactness in the original dimension.
---

Suppose `B in U(d)` has, for every `M`, conjugates
`X_1,...,X_M` satisfying

```text
||X_i^3-I||_2 <= epsilon,
||(X_i X_j)^2-I||_2 <= epsilon             for i!=j.    (CPF1)
```

Then

```text
||B-I||_2 <= 2 epsilon.                                  (CPF2)
```

Consequently `thompson-v-r5-coherent-carmichael-family` implies that the
Bleak--Quick generator `b=(01 10 11)` satisfies

```text
||U(b)-I||_2 <= 2 C def_R(U)
```

in every finite-dimensional presentation model.
