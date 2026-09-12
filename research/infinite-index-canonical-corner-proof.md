---
rg: 2
id: infinite-index-canonical-corner-proof
kind: route
title: Orthogonal translates of a positive projection cannot fit in finite trace
target: infinite-index-canonical-subgroup-corner-is-impossible
requires: []
---

Suppose `p` satisfied `(ISC1)`.  For a left coset `gH`, define

```text
p_(gH)=alpha_g(p)=u_g p u_g^*.
```

This is well-defined because `p` is `H`-invariant.  If `gH != kH`, then
`a=g^(-1)k` is not in `H`.  The second part of `(ISC1)` gives

```text
0 = p u_a p u_a^* = p alpha_a(p).
```

Conjugating by `u_g` yields `p_(gH) p_(kH)=0`.  Hence the family
`{p_(gH):gH in Lambda/H}` is an infinite family of pairwise orthogonal
projections.  Trace invariance gives

```text
tau(p_(gH))=tau(p)>0
```

for every coset.  The trace of the sum of any `n` of them is therefore
`n tau(p)`, contradicting finiteness once `n>1/tau(p)`.

For the standard induced algebra with counting measure this argument does
not contradict anything: its trace is semifinite and the base-coset
projection has finite trace.  It shows exactly why that Morita corner cannot
be transplanted to a probability/Haar crossed product at infinite index.
