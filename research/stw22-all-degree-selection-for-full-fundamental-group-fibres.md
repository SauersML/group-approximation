---
rg: 2
id: stw22-all-degree-selection-for-full-fundamental-group-fibres
kind: route
title: Apply finite-degree Michael selection to one full-fundamental-group fibre
target: stw22-full-fundamental-group-trivial-bundles-finite-dimensional
requires:
  - stw22-full-fundamental-group-weighted-copy-all-sphere-fillings
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-full-fundamental-group-all-degree-audit-2026-08-30.md
---

Put `d=dim(K)`.  The Hilbert `C(K)`-module of the trivial bundle is
`C(K,L^2(N))`; it is countably generated because `L^2(N)` is separable.
For a fixed positive contraction `a`, replication number `m`, and uniform
strict support slack, the exact weighted-copy multifunction

```text
x |-> F_(N,m)(a(x)) subset L^2(N)^m
```

has nonempty closed values and is lower semicontinuous by the finite-factor
weighted correction lemma.  When `d>=1`,
`stw22-full-fundamental-group-weighted-copy-all-sphere-fillings` makes the
values globally `(d-1)`-connected and uniformly equi-`LC^(d-1)` in this
one complete Hilbert space: for a requested output radius, take the minimum
of the finitely many degree-wise input moduli for `0<=j<=d-1`.  The standard
fibre-centred-to-ambient-centred
conversion and the equivalence of maximum and Hilbert-sum metrics are
harmless because `m` is fixed.  Michael's theorem with `n=d-1` gives an
exact continuous tuple over `K`.  For `d=0`, use the established clopen
selection argument.

Given a positive element of a norm-fibre gap, make a spectral cut and a
central cutoff supported where the fibre support trace is less than
`1/(2m)`.  The preceding selection gives `m` exact orthogonal copies of
the resulting globally slack contraction.  Every bounded positive trace
on the gap is therefore at most its norm divided by `m`.  Let `m` tend to
infinity and then remove the spectral cut.  All bounded positive gap traces
vanish, so the exact fibre-gap criterion gives the displayed integral
formula and uniform `2`-continuity.
