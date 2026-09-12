---
rg: 2
id: stw82-traces-block-unit-coupled-colour-reduction
kind: claim
title: Traces forbid colour reduction by full-unit coupled partitions
artifacts:
  - research/artifacts/stw82-order-zero-spectral-subdivision-audit-2026-08-30.md
distinct_from:
  stw82-scalar-band-depth-floor: that obstruction is pointwise and commutative for independent scalar partitions; this applies to operator-valued coupled partitions and uses only one tracial state.
---

Let `B` be a unital C*-algebra with a tracial state.  Suppose positive
contractions `c_(v,k) in B`, indexed by finite sets `V` and
`k=1,...,d`, satisfy

```text
sum_(k=1)^d c_(v,k)=1_B                    (v in V)
```

and

```text
c_(v,k)c_(w,k)=0                           (v!=w).
```

Then `|V|<=d`.

Consequently the full-unit hypotheses in
`stw82-coupled-operator-partitions-merge-colours` cannot reduce the number
of original colours in any unital tracial target.  A coupled construction
which can address arbitrary nuclear extensions must cover the support of
each outgoing colour rather than partition the whole multiplier unit once
for every colour.
