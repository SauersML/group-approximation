---
rg: 2
id: strict-idempotent-equivalence-breaks-direct-finiteness
kind: claim
title: A strict Murray-von Neumann compression forces failure of direct finiteness
distinct_from:
  leavitt-corner-one-sided-lift-exists: that is an open search for a particular one-sided pair in the Leavitt corner whose reverse defect survives evaluation; this is a general established ring criterion requiring a strict equivalence of idempotents.
  leavitt-primitive-corner-recursive-extension: that is a nonunital self-embedding into a proper corner and does not identify the source identity with the corner idempotent; this requires exactly such a strict idempotent equivalence and therefore has a direct-finiteness consequence.
artifacts:
  - research/artifacts/leavitt-packet-trace-and-compression-2026-08-24.md
---

Let `T` be a unital ring.  If idempotents `q<p` are Murray--von Neumann
equivalent, meaning there exist

```text
x in pTq,        y in qTp,        xy=p,        yx=q,
```

then `T` is not directly finite.

In particular, it is sufficient to have an idempotent `p != 0` and a unit
`w in T^x` such that `q=wpw^(-1)` is a strict subidempotent of `p`: take
`x=pw^(-1)q` and `y=qwp`.
