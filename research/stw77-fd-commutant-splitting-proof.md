---
rg: 2
id: stw77-fd-commutant-splitting-proof
kind: route
title: Compress central isometries and transport corner splittings through matrix units
target: stw77-fd-commutant-splitting-iff-proper-supports
requires: []
---

Suppose first that `s_0,s_1 in B intersect D'` are isometries with orthogonal
ranges.  For a minimal projection `p_j in D`, put

```text
v_(i,j)=s_i p_j=p_j s_i.
```

Then

```text
v_(i,j)^* v_(i,j)=p_j,
v_(0,j)v_(0,j)^* orthogonal v_(1,j)v_(1,j)^* <= p_j.
```

Hence every `p_j` is properly infinite.

Conversely, choose matrix units `(e^(j)_(ab))` with
`p_j=e^(j)_(11)`.  Proper infiniteness supplies, for `i=0,1`, elements
`w_(i,j) in p_j B p_j` such that

```text
w_(i,j)^*w_(i,j)=p_j,
w_(0,j)w_(0,j)^* orthogonal w_(1,j)w_(1,j)^* <= p_j.
```

Transport these corner isometries across the matrix block and sum:

```text
s_i=sum_j sum_(a=1)^(n_j) e^(j)_(a1) w_(i,j) e^(j)_(1a).
```

Matrix-unit multiplication gives `s_i^*s_i=1`, orthogonality of the two
range projections, and

```text
s_i e^(j)_(ab)=e^(j)_(ab)s_i
```

for all `a,b,j`.  Thus `s_0,s_1` lie in `B intersect D'`.

Minimal projections within one matrix summand are Murray--von Neumann
equivalent through its matrix units, so proper infiniteness of one is
equivalent to proper infiniteness of every choice.
