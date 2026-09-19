---
rg: 2
id: stw27-stable-range-endpoint-division-proof
kind: route
title: Put the reduced K-class into two Bezout bundles and cancel in stable range
target: stw27-stable-range-endpoint-division
requires:
  - complex-bundles-realize-and-cancel-in-stable-range
artifacts:
  - research/artifacts/stw27-dimension-drop-high-rank-audit-2026-08-30.md
---

Let

```text
delta=[E]-M[1] in reduced K^0(X).
```

The complex vector-bundle stable-range theorem has two consequences for a
finite `d`-dimensional CW complex, with `D=ceil(d/2)`:

1. every `K^0`-class of rank at least `D` is represented by a vector bundle
   of that rank;
2. two vector bundles of the same rank at least `D` are isomorphic whenever
   their `K^0`-classes agree.

Every integer `R>=n(n-1)` is of the form `na+(n+1)b` with `a,b>=0`.
Indeed, write `R=qn+r` with `0<=r<n`. The lower bound gives
`q>=n-1>=r`, and

```text
R=(q-r)n+r(n+1).
```

Hypothesis `(H)` therefore gives

```text
M-(2n+1)D = na+(n+1)b
```

for some `a,b>=0`.  Put `f=D+a` and `g=D+b`.  Then

```text
M=nf+(n+1)g.                                          (6)
```

The two stable classes

```text
f[1]-delta,                 g[1]+delta
```

have ranks `f,g>=D`.  Choose vector bundles `F,G` representing them.  A
direct calculation in `K^0(X)` gives

```text
n[F]+(n+1)[G]
 = n(f[1]-delta)+(n+1)(g[1]+delta)
 = M[1]+delta
 = [E].                                               (7)
```

Both sides of `(7)` are represented by bundles of rank `M>=D`.  Stable-range
cancellation upgrades `(7)` to the bundle isomorphism `(2)`.

The two comparisons in `(3)` are now literal summand inclusions:

```text
n(F direct_sum G) <= nF direct_sum (n+1)G = E,
E = nF direct_sum (n+1)G <= (n+1)(F direct_sum G).
```

Finally identify `(2)` with

```text
(F tensor C^n) direct_sum (G tensor C^(n+1)).
```

On the first summand let `Z_(n,n+1)` act through evaluation at the
`M_n` endpoint, and on the second let it act through evaluation at the
`M_(n+1)` endpoint.  Conjugating this direct-sum action by `(2)` proves
`(4)`.

For the final equivalence, the reverse implication is the construction just
given.  Conversely, a representation factoring through
`M_n direct_sum M_(n+1)` splits `E` by the images of the two central unit
projections.  A vector bundle carrying a unital `M_k`-action is, by the
Morita equivalence between `M_k` and the scalars, of the form
`H tensor C^k`.  Applying this to the two central summands gives
`E isomorphic to nF direct_sum (n+1)G`.
