---
rg: 2
id: stw22-finite-dimensional-colouring-from-local-lifts
kind: claim
title: Finite-dimensional colouring turns local weighted lifts into fibre-gap trace vanishing
distinct_from:
  stw22-zero-dimensional-trivial-field-trace-continuity: that theorem produces one global weighted embedding into each fixed corner by clopen selection; the present theorem permits topological twisting and pays exactly d+1 coloured source pieces.
  stw22-tracefree-fibre-gap-ideals-force-trace-continuity: that theorem is an abstract trace-free-gap criterion; the present theorem verifies it by a dimension-coloured weighted-embedding construction for a concrete class.
  stw22-derived-set-gap-trace-reduction: that theorem is organized by Cantor--Bendixson rank and applies only to scattered bases; the present theorem is organized by covering dimension and includes connected finite-dimensional bases.
artifacts:
  - research/artifacts/stw22-finite-dimensional-coloured-selection-audit-2026-08-30.md
---

Let `X` be compact and metrizable with finite covering dimension `d`, let
`U` be an infinite-dimensional UHF algebra with unique trace, and let `M`
be the uniform tracial completion of `C(X) tensor U`.  Assume:

```text
(LWCL) If e in R is a projection, s<tau(e), and
       a:Z->R_+ is a bounded 2-norm-continuous field on a closed
       subspace Z of X with tau(supp(a(z)))<=s, then every point of Z
       has a neighbourhood O carrying a 2-norm-continuous w with
       w^*w=a and supp(ww^*)<=e.
```

Then every fibre gap

```text
K_x/J_x
```

has no nonzero bounded positive trace.  Consequently every tracial state on
`M` is uniquely

```text
a |-> integral_X tau(a(t)) dmu(t)
```

for a probability measure `mu` on `X`, and is continuous for the uniform
`2`-norm.

The quantitative local-to-global statement is the following.  Let `c` be a
positive contraction in `K_x`, supported in a neighbourhood `V` of `x`, and
suppose

```text
sup_(t in V) tau(supp(c(t))) < 1/m.                      (FDS)
```

There are elements

```text
v_(j,r) in K_x,       1<=j<=m, 0<=r<=d,
```

such that

```text
sum_(r=0)^d v_(j,r)^*v_(j,r)=c             (1<=j<=m),
||sum_(j=1)^m sum_(r=0)^d v_(j,r)v_(j,r)^*||<=d+1.      (FDC)
```

Thus every bounded positive trace `sigma` on the gap satisfies

```text
m sigma(c) <= (d+1)||sigma||.                            (FDT)
```

The dimension cost is independent of `m`, so arbitrary replication still
forces `sigma(c)=0`.  The construction uses local square-root-weighted
embeddings into fixed orthogonal factor corners and a `(d+1)`-colourable
refinement.  It does not require a globally continuous choice of the
jumping spectral support.

Thus finite covering dimension creates no further obstruction after
`(LWCL)` is available.  The sequential lower-lifting statement `(WCL)` in
`stw22-select-weighted-corner-embeddings-over-clopens-proof` is enough for
the clopen approximation used in the zero-dimensional theorem, but does
not by itself imply an exact parametrized local section on a
positive-dimensional neighbourhood.  No unconditional
positive-dimensional assertion is made here.  For a nontrivial tracial
bundle, fixed global comparison corners would be an additional issue.
