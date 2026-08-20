---
rg: 2
id: bcs-corner-model-is-a-compatible-projection-atlas
kind: claim
title: A unital BCS model in an algebraic corner is exactly a compatible context projection atlas
artifacts:
  - research/artifacts/signed-hecke-direct-trace-promotion-2026-08-20.md
distinct_from:
  non-ce-bcs-has-finite-dimensional-forbidden-mass-gap: that gives a quantitative obstruction to approximate finite-dimensional BCS tuples; this is an exact algebraic equivalence describing the group-corner data that would contradict that obstruction through the canonical trace.
---

Let a finite BCS have variables `X`, contexts `c`, context variable sets
`U_c`, and allowed assignments `R_c subset {+1,-1}^(U_c)`. Let `q` be an
algebraic projection in a star algebra `A`.

There is a unital star homomorphism from the BCS algebra to `qAq` if and only
if there are algebraic projections

```text
(p_(c,a))_(a in R_c),             sum_(a in R_c)p_(c,a)=q,   (BPA1)
```

orthogonal within each context, such that the signed marginals

```text
V_(c,x)=sum_(a in R_c) a_x p_(c,a)                          (BPA2)
```

obey the overlap equations

```text
V_(c,x)=V_(d,x)       whenever x in U_c intersect U_d.      (BPA3)
```

Given the atlas, `(BPA3)` defines one element `V_x`. Within a context the
`V_x` are commuting self-adjoint involutions relative to `q`, and every
forbidden joint atom vanishes. Conversely, from any BCS corner model take
the allowed joint spectral projections in each context; they satisfy
`(BPA1)--(BPA3)`.

For `A=C[Gamma]`, this turns the signed-Hecke groupification problem into a
finite list of algebraic projection identities. Together with
`piecewise-group-transport-gives-corner-unitaries`, the projections and their
transport arrows may all have finite group-word support.
