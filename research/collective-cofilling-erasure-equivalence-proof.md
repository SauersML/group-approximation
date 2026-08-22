---
rg: 2
id: collective-cofilling-erasure-equivalence-proof
kind: route
title: Apply collective filling to all erased syndromes at once
target: collective-cofilling-is-common-erasure-cleaning
requires: []
---

Assume `(CCF1)` and fix `E`.  Take as the finite family all syndromes

```text
beta in im(d) cap F_2^E.
```

Choose simultaneous fillings `a_beta` by `(CCF1)` and set
`S=union_beta supp(a_beta)`.  Their syndrome supports have union contained
in `E`, so `|S|<=mu|E|`.  If `x` has `supp(dx) subset E`, then
`beta=dx` occurs in the family and

```text
x=(x+a_beta)+a_beta in ker(d)+F_2^S.
```

This proves `(CCF2)`.

Conversely, assume `(CCF2)` and take any finite attainable family
`(beta_t)`.  Set `E=union_t supp(beta_t)` and choose arbitrary `x_t` with
`d x_t=beta_t`.  By `(CCF2)`, write `x_t=c_t+a_t`, where `c_t in ker(d)`
and every `a_t` is supported on the same `S(E)`.  Then `d a_t=beta_t` and

```text
|union_t supp(a_t)| <= |S(E)| <= mu |E|,
```

which is `(CCF1)`.

Kaufman--Tessler prove uniform collective cofilling for bounded-degree
Ramanujan complexes.  Their norms are weighted Hamming norms, but bounded
upper and lower incidence degree compares those norms to counting support
by constants independent of the complex size, yielding the displayed
unweighted form after changing `mu` by a fixed factor.
