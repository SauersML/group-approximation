---
rg: 2
id: stw74-relative-grassmannian-extension-proof
kind: route
title: Translate constrained projections into relative Grassmannian and K-theory extension problems
target: stw74-relative-grassmannian-bundle-threshold
requires:
  - stw74-finite-point-ranks-no-topological-obstruction
artifacts:
  - research/artifacts/stw74-property-sp-cu-stability-audit-2026-08-30.md
---

## Exact fixed-matrix criterion

Let `q in M_k(B_p)` be a nonzero projection.  Connectedness of `X` makes its
rank a positive constant `d`.  On `Y`, membership in the matrix algebra over
the one-dimensional field `C p(y)` gives a unique projection field

```text
a in C(Y,M_k),                 q|Y=a tensor p.           (1)
```

Since `Y` is connected, `a` has one rank `alpha`, with `1<=alpha<=k`, and
`d=alpha r`.  The projection `q` is exactly an extension of the map `(GE)`
to `Gr_d(C^(km))`.

Conversely, any extension of `(GE)` is a projection
`q in C(X,M_(km))` whose restriction has the form (1), and hence lies in
`M_k(B_p)`.  This proves the necessary-and-sufficient unstable criterion.
Notice the difference from finitely many constrained fibres: there one may
correct independently by localized unitary paths; here the entire
Grassmannian map on `Y` must extend coherently.

## Stable range and the relative K-boundary

We use the standard complex Grassmannian stable-range theorem: if `Z` is a
finite CW complex of dimension at most

```text
2 min(d,M-d),
```

then the map

```text
[Z,Gr_d(C^M)] -> {xi in K^0(Z):rank(xi)=d}              (2)
```

which sends a projection to its bundle class is bijective.  One way to see
the bound is to stabilize first `Gr_d(C^M)->BU(d)`, whose missing Schubert
cells begin above degree `2(M-d)`, and then `BU(d)->BU`, whose unstable cells
begin above degree `2d`.

An extension of `(GE)` plainly gives a lift of `[A tensor E_p]` to `K^0(X)`.
Conversely suppose the class lifts.  Since `Y` is nonempty and `X` is
connected, the lift has rank `d`.  Apply (2) on `X` to represent it by a map

```text
g:X->Gr_d(C^M).
```

The restriction `g|Y` and `(GE)` have the same `K^0(Y)` class.  The same
stable-range theorem on `Y` makes them homotopic.  Because `(X,Y)` is a CW
pair, the homotopy extension property changes `g` through a homotopy so that
its final restriction is exactly `(GE)`.  This proves `(K)`.  Exactness of
the relative topological `K`-theory sequence identifies `(K)` with vanishing
of the boundary

```text
K^0(Y) -> K^1(X,Y).                                    (3)
```

## Why dimension two is still unobstructed

For `0<d<M`, the complex Grassmannian `Gr_d(C^M)` is path connected and
simply connected.  Starting with a map on the subcomplex `Y`, extend over
the relative cells of `(X,Y)`.  Path connectedness removes the obstruction
on one-cells and simple connectedness removes it on two-cells.  Thus every
projection field on a subcomplex of a finite `2`-complex extends at the same
matrix level.  For `d=M` the target is a point, so the assertion is immediate.

## The first topological threshold jump

Let `p:S^2->Gr_1(C^2)=CP^1` classify the Bott line `H`, and form `B_p` over
the pair `(D^3,S^2)`.  A nonzero projection in `B_p` would have rank one and
restrict to `p`, because the only nonzero projection in the scalar algebra
over `p(y)` is `p(y)` itself.  Such a projection would extend the degree-one
map `S^2->CP^1` across `D^3`, which is impossible.  Therefore `B_p` is
projectionless.

At level two let `a=1-p`, viewed as a rank-one projection in `M_2(C(S^2))`.
Its line bundle is the complement `H^perp`, with

```text
c_1(H^perp)=-c_1(H).
```

Consequently

```text
c_1(H^perp tensor H)=0.
```

Complex line bundles over `S^2` are classified by their first Chern class,
so `H^perp tensor H` is trivial.  Equivalently, the map

```text
a tensor p:S^2->Gr_1(C^4)=CP^3
```

is null-homotopic and extends over `D^3`.  The exact criterion produces a
nonzero projection in `M_2(B_p)`.  Since level one is empty, the first level
is exactly two.
