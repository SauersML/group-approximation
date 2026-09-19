---
rg: 2
id: stw22-cofinite-corona-calculation-at-rank-one-points-proof
kind: route
title: Localize at a rank-one point and orthogonalize in each discrete coordinate
target: stw22-rank-one-scattered-fibre-gaps-are-tracefree
requires:
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-rank-one-scattered-gap-audit-2026-08-30.md
---

The uniform completion `M` is the algebra of operator-norm-bounded maps

```text
a:X -> R
```

which are continuous for the `2`-norm metric.  One inclusion is immediate.
For the converse, approximate the compact `2`-norm image of `a` by finitely
many elements of `U`, and combine those approximants with a partition of
unity on `X`.  This gives uniform `2`-norm approximation by elements of
`C(X) tensor U`, with a common operator-norm bound.

In the norm fibre at `x`, the central projection `1_V` is the identity,
because `1-1_V` vanishes on a neighbourhood of `x` and hence belongs to
`J_x`.  We may therefore replace `X` by `V`.  Since every point of `D` is
isolated, restriction identifies `M` with the bounded families

```text
(a_x,(a_d)_(d in D)) in R x product_D R
```

such that `||a_d-a_x||_2 -> 0` along the cofinite filter.  Evaluation at
`x` gives

```text
K_x={a:a_x=0}.
```

Products by continuous scalar functions vanishing at `x` have coordinate
norms tending to zero.  Conversely, if `a in K_x` and
`||a_d|| -> 0` cofinitely, deleting finitely many coordinates approximates
`a` in norm by a product with a scalar function which vanishes on a
neighbourhood of `x`.  Hence

```text
J_x={a in K_x:||a_d|| -> 0 cofinitely},
```

which proves `(RSG)`.

We now prove that `I_D` is bounded-trace-free.  Let `sigma` be a bounded
positive trace on `I_D`, and let `a=[(a_d)]` be a positive contraction.
For `epsilon>0`, put

```text
b_d=(a_d-epsilon)_+,
p_d=1_(epsilon,infinity)(a_d).
```

Chebyshev gives

```text
tau(p_d) <= epsilon^(-2)||a_d||_2^2 -> 0
```

cofinitely.  Fix `m`.  Outside a finite set, the finite factor `R` contains
`m` pairwise orthogonal projections unitarily equivalent to `p_d`.
Choose the implementing unitaries independently in each coordinate.  They
give `m` pairwise orthogonal conjugates `b^(1),...,b^(m)` of `b` in the
corona; the exceptional finite coordinates vanish in the `c_0` quotient.
A bounded trace on an ideal is invariant under unitaries of the containing
algebra, by its canonical extension to the multiplier algebra.  Therefore

```text
m sigma(b)=sigma(sum_(j=1)^m b^(j)) <= ||sigma||.
```

As `m` is arbitrary, `sigma(b)=0`.  Since `||a-b||<=epsilon`, letting
`epsilon` decrease to zero gives `sigma(a)=0`; hence `sigma=0`.

If `D` is countably infinite, enumerate distinct points `d_n` and choose
projections `p_(d_n)` of trace `1/n`, putting zero at all remaining
coordinates.  Their family is `2`-norm null cofinitely but not norm null,
so `(RSG)` is nonzero.

Finally suppose `X^(2)` is empty.  The compact discrete space `X^(1)` is
finite.  Each point of `X^(1)` has a clopen neighbourhood meeting `X^(1)`
only there, hence has the form used above; each point outside `X^(1)` is
isolated and has `J_x=K_x`.  Every fibre gap is therefore bounded-trace-free.
The expectation

```text
E(a)(t)=tau(a(t))
```

has unique-trace factor fibres `R`, so
`stw22-tracefree-fibre-gap-ideals-force-trace-continuity` gives the claimed
description of all traces.  For a general scattered `X`, the same argument
eliminates every point outside `X^(2)` and makes no assertion at higher-rank
points, where coordinatewise conjugators must be glued across non-discrete
punctured neighbourhoods.
