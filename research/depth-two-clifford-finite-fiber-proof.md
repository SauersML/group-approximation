---
rg: 2
id: depth-two-clifford-finite-fiber-proof
kind: route
title: Identify the square-zero congruence kernel and take full fibers over coweight boxes
target: depth-two-clifford-types-form-a-finite-fiber-folner-graph
requires:
  - exact-dyadic-conductor-band-has-uniform-parahoric-overlap-loss
  - six-parahoric-finite-fiber-folds-remain-amenable
---

For `I=2^(a-2)(Z/2^a Z)` one has `I^2=0`.  Hence multiplication and
determinant in the principal kernel are

```text
(1+X)(1+Y)=1+X+Y,
det(1+X)=1+tr(X),                                      (DCF6)
```

which proves `(DCF2)`.  If `g in Q_a`, then

```text
g(1+2^(a-2)X)g^(-1)
 =1+2^(a-2)(gXg^(-1)),                                 (DCF7)
```

and the right side depends only on `g mod 4`.  Thus the conjugation action
factors through `Q_2`.  Clifford theory for the finite abelian normal
subgroup `N_a` says that the restriction of an irreducible `Q_a`-module is
supported on one `Q_2`-orbit in `N_a^hat`; this proves the finite,
level-independent type set `(DCF3)`.

Each denominator direction changes the coweight coordinate by one of the
six fixed vectors and induces a relation between two elements of the finite
set `F`.  Thus a radius-`R` graph ball has at most `|F| O(R^2)` vertices.
A bounded-degree infinite graph with a uniform polynomial upper bound on
ball growth is amenable: a positive Cheeger constant would force
exponential growth of every ball.  In the full finite-fiber system, the
sharper box computation of
`six-parahoric-finite-fiber-folds-remain-amenable` gives `(DCF5)` directly.
