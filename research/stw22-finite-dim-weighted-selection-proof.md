---
rg: 2
id: stw22-finite-dim-weighted-selection-proof
kind: route
title: Apply all-degree Michael selection and finite-dimensional colouring
target: stw22-finite-dimensional-trivial-field-traces
requires:
  - stw22-weighted-purification-all-sphere-fillings
  - stw22-finite-dimensional-colouring-from-local-lifts
  - stw22-one-dimensional-trivial-field-trace-continuity
artifacts:
  - research/artifacts/stw22-all-degree-weighted-selection-audit-2026-08-30.md
---

Let `d=dim(X)<infinity`.  The proof of
`stw22-one-dimensional-trivial-field-trace-continuity` establishes, without
using the dimension bound, that for fixed `s<tau(e)` the multifunction

```text
F(a)={w in eR:w^*w=a},
0<=a<=1,       tau(supp(a))<=s,                         (FD1)
```

has nonempty closed values in the complete metric space

```text
E_e={w in eR:||w||<=1}
```

with its `2`-norm, and is lower semicontinuous as `a` varies in `2`-norm.

If `d>=1`, `stw22-weighted-purification-all-sphere-fillings` says that the
family `(FD1)` is equi-`LC^(d-1)` and each value is
`(d-1)`-connected.  Michael's *Continuous Selections II*, Theorem 1.2,
applies with `n=d-1` to every closed subspace `Z` of `X`: it is compact
metrizable, `dim(Z)<=d=n+1`, the target `E_e` is complete, and the
multifunction has precisely the nonempty closed, lower-semicontinuous,
equi-`LC^n`, `n`-connected values required by the theorem.  Therefore every
`2`-norm-continuous positive field `a:Z->R` satisfying the support bound in
`(FD1)` has a global continuous weighted purification into `e`.  For
`d=0`, the established clopen selection theorem gives the same conclusion.

In particular the local weighted corner-lifting hypothesis `(LWCL)` in
`stw22-finite-dimensional-colouring-from-local-lifts` holds for `X`.
Apply that theorem with the actual dimension `d`.  Its `(d+1)`-colour
replication estimate gives, for every bounded positive trace `sigma` on a
fibre gap and every positive spectral cut `c`,

```text
m sigma(c)<=(d+1)||sigma||
```

for every `m`.  Letting `m` tend to infinity and then removing the spectral
cut shows that every bounded gap trace vanishes.  The abstract trace-free
gap criterion then gives the asserted integral description and uniform
`2`-norm continuity of every trace on `M`.
