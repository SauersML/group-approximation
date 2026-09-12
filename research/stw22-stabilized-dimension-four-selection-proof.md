---
rg: 2
id: stw22-stabilized-dimension-four-selection-proof
kind: route
title: Use only half-slack replication values in degree-three stabilized selection
target: stw22-dim4-factor-bundles-have-uniform-traces
requires:
  - stw22-dim1-factor-bundles-have-uniform-traces
  - stw22-half-slack-all-factor-weighted-copy-uniform-s3-fillings
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-dim4-factor-bundle-breakthrough-2026-08-31.md
---

The trace-gap argument does not need selection for every strictly slack
weight. It only needs the following half-slack case. Fix `m>=2` and a
positive contraction `a in M` with

```text
m tau_x(supp(a_x))<=1/2             for every x in K.  (AF4-6)
```

Stabilization puts the exact weighted-copy values `F_x(a)` into the one
complete Hilbert space `(ell^2)^m`. The established finite-factor
correction theorem makes them nonempty, closed in the fibre operator
balls, and lower semicontinuous, uniformly across all finite factor types.
Countable generation makes every diffuse fibre separable-predual.

The universal path, loop, two-sphere, and half-slack three-sphere theorems
give common local moduli in degrees `0,1,2,3` and global three-connectivity
of every value. For fixed `m`, maximum and Hilbert-sum tuple metrics are
uniformly equivalent, so the ambient-centre conversion gives an
equi-`LC^3` family in `(ell^2)^m`.

Michael's finite-dimensional theorem with `n=3` applies because `K` is
paracompact, `dim(K)<=4`, and the values are nonempty, closed,
three-connected, lower semicontinuous, and equi-`LC^3`. The resulting
exact continuous tuple belongs to the Hilbert-module completion; the
operator-ball recovery identity puts every component in `M_1`.

Now choose a positive contraction lift `b in K_(x_0)` of a positive
fibre-gap class, fix `epsilon>0`, and let `m>=2` be arbitrary. For
`c=(b-epsilon)_+`, Chebyshev gives a neighbourhood of `x_0` on which

```text
tau_y(supp(c_y))<1/(2m).                               (AF4-7)
```

A central cutoff equal to one near `x_0` and zero off that neighbourhood
does not change the gap class and turns `c` into a global weight satisfying
(AF4-6). Select `m` exact copies. Their orthogonal range positives sum to
a positive contraction, so every bounded positive gap trace `sigma` obeys

```text
m sigma([c])<=||sigma||.                               (AF4-8)
```

Let `m` tend to infinity through integers at least two, and then let
`epsilon` decrease to zero. Every positive gap trace vanishes. The exact
fibre-gap criterion gives (AF4-5).

No type-continuity is used. At each point, (AF4-6) either puts a nonzero
matrix fibre in codimension at least two or invokes the diffuse theorem;
the lower-semicontinuous graph itself was already proved type-free.