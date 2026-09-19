---
rg: 2
id: stw22-fixed-factor-dimension-three-selection-proof
kind: route
title: Apply degree-two Michael selection to the fixed-factor weighted fibres
target: stw22-dim3-trivial-factor-bundles-have-uniform-traces
requires:
  - stw22-fixed-factor-weighted-copy-uniform-s2-fillings
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-fixed-factor-s2-filling-audit-2026-08-30.md
---

For a fixed positive contraction `a in C_sigma(K,N)`, replication number
`m`, and uniform strict support slack, regard the exact weighted-copy sets
`F_x(a)` as subsets of the one complete Hilbert space `L^2(N)^m`.  The
finite-factor correction lemma makes `x |-> F_x(a)` lower semicontinuous;
the values are nonempty and closed.

The path and loop theorems give uniform equi-`LC^0` and equi-`LC^1`.
`stw22-fixed-factor-weighted-copy-uniform-s2-fillings` supplies equi-`LC^2`
and global `2`-connectivity.  The standard ambient-centre conversion and
the equivalence of maximum and Hilbert-sum tuple metrics apply for the fixed
`m`.  Michael's finite-dimensional selection theorem with `n=2` therefore
produces a continuous exact weighted-copy tuple over `K` when `dim(K)<=3`.
The selected contractions are, by definition, elements of
`C_sigma(K,N)`.

The usual spectral cut and central cutoff near a chosen base point give a
globally slack positive contraction representing any prescribed positive
gap element.  Selecting `m` orthogonal copies bounds every positive gap
trace by its norm divided by `m`.  Letting `m` tend to infinity and then
removing the spectral cut kills every bounded positive gap trace.  The
exact fibre-gap criterion yields the stated trace formula.
