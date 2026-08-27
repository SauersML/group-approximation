---
rg: 2
id: every-fixed-dyadic-clifford-window-folner-proof
kind: route
title: Linearize the deepest fixed congruence window and take coweight boxes
target: every-fixed-dyadic-clifford-window-is-finite-fiber-folner
requires:
  - six-parahoric-finite-fiber-folds-remain-amenable
---

Let `t=2^(a-k)`.  Since `a>=2k`, one has `t^2=0 mod 2^a`.  Hence

```text
(1+tX)(1+tY)=1+t(X+Y) mod 2^a.                          (FDP1)
```

The determinant expansion has no terms of degree at least two, so

```text
det(1+tX)=1+t tr(X) mod 2^a.                            (FDP2)
```

Thus `1+tX` lies in `Q_a` exactly when `tr(X)=0 mod 2^k`, and `(FDP1)`
identifies `N_(a,k)` with the additive group `sl_3(Z/2^k Z)`.

For `g in Q_a`,

```text
g(1+tX)g^(-1)=1+t(gXg^(-1)) mod 2^a.                   (FDP3)
```

The coefficient on the right is read modulo `2^k`; it therefore depends
only on `g mod 2^k`.  This proves that the conjugation action factors through
`Q_k`.  Clifford theory for the finite abelian normal subgroup `N_(a,k)`
says that the characters occurring in the restriction of one irreducible
`Q_a`-module form one `Q_k`-orbit.  The possible orbit labels are consequently
the fixed finite set `(FDC3)`.

Each of the finitely many named arithmetic moves changes the coweight by a
vector in a fixed finite subset of `Z^2` and changes the second coordinate
inside `F_k`.  A graph ball of radius `R` therefore has at most
`|F_k| O_k(R^2)` vertices.  An infinite bounded-degree graph with a positive
Cheeger constant has exponential ball growth, so every infinite component
is amenable.  For the full finite-fiber transition system, taking all of
`F_k` over a square coweight box gives `(FDC4)` directly, exactly as in
`six-parahoric-finite-fiber-folds-remain-amenable`.
