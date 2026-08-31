---
rg: 2
id: stw22-stabilized-finite-dimensional-selection-proof
kind: route
title: Select only an unbounded stable replication tail in the degree dictated by the base
target: stw22-finite-dimensional-factor-bundles-have-uniform-traces
requires:
  - stw22-dim1-factor-bundles-have-uniform-traces
  - stw22-dim2-factor-bundles-have-uniform-traces
  - stw22-half-slack-all-factor-weighted-copy-finite-degree-fillings
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-all-factor-finite-dimensional-breakthrough-2026-08-31.md
---

Put `D=dim(K)<infinity`. The cases `D<=2` are the established stabilized
selection theorem. Suppose `D>=3` and set

```text
j=D-1,       M_D=ceil(j/2).                              (AFD-6)
```

Fix any `m>=M_D` and any positive contraction `a in M` satisfying

```text
m tau_x(supp(a_x))<=1/2             for every x in K.   (AFD-7)
```

The existing stabilization and correction theorem realizes the exact
weighted-copy values as nonempty closed lower-semicontinuous subsets of one
complete Hilbert space, uniformly across all finite factor types, and
supplies operator-ball recovery. Countable generation makes every diffuse
fibre separable-predual.

By the half-slack finite-degree theorem, the values are `j`-connected and
equi-`LC^j`, with a common modulus for this fixed `D`. Compact Hausdorff
spaces are paracompact, and `dim(K)=D=j+1`, so Michael selection with index
`j` gives a continuous exact `m`-tuple. Operator-ball recovery returns
it to `M_1^m`. Factor type may change because lower semicontinuity and all
degreewise moduli are type-free.

Now fix `x_0 in K`, a bounded positive trace `sigma` on the fibre gap
`K_(x_0)/J_(x_0)`, a positive contraction lift `b in K_(x_0)`, and
`epsilon>0`. For every arbitrarily large integer `m>=M_D`, two-nullity
of `b` at `x_0` gives a neighbourhood `U_m` on which

```text
tau_y(supp((b-epsilon)_+(y)))<1/(2m).                   (AFD-8)
```

Choose a central cutoff equal to one on a neighbourhood of `x_0` and
vanishing off `U_m`. Multiplying `(b-epsilon)_+` by it gives a global
half-slack weight `a_m` with the same class in
`K_(x_0)/J_(x_0)`. Select `m` exact copies. Their pairwise orthogonal
range positives have a sum which is a positive contraction, so traciality
gives

```text
m sigma([(b-epsilon)_+])
 =sigma([sum_(i=1)^m v_i v_i^*])<=||sigma||.            (AFD-9)
```

Let `m` tend to infinity through this unbounded tail, then let
`epsilon` decrease to zero. Every positive fibre-gap trace vanishes. The
gap criterion yields (AFD-5). Only one fixed finite Michael index and one
fixed degreewise modulus are used for each base; no uniform-in-`D` or
infinite-dimensional selection statement occurs.
