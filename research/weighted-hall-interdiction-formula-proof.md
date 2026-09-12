---
rg: 2
id: weighted-hall-interdiction-formula-proof
kind: route
title: Every deficient graph exposes a cut whose crossing deletions were necessary
requires: []
target: weighted-hall-interdiction-formula
---

For any pair `(S,T)` appearing in `(WHI1)`, delete every baseline edge from
`S` to `R\T`.  Then

```text
N_(G-F_(S,T))(S) subset T,
```

and therefore

```text
alpha(S) > beta(T) >= beta(N_(G-F_(S,T))(S)).          (I1)
```

So `F_(S,T)` really creates a weighted Hall deficit, proving that the optimum
deletion cost is at most `(WHI1)`.

Conversely suppose `F subset E` creates a deficit.  Choose a source set `S`
with

```text
alpha(S) > beta(N_(G-F)(S))
```

and put `T=N_(G-F)(S)`.  If an original edge `(i,j) in E` has `i in S` and
`j notin T`, then that edge cannot remain in `G-F`, by the definition of the
neighbor set.  Hence

```text
E intersect (S x (R\T)) subset F.                    (I2)
```

Nonnegativity of the deletion costs gives

```text
cost(F) >= cost(F_(S,T)).                             (I3)
```

The pair `(S,T)` is admissible in `(WHI1)`, so every deficit-producing deletion
has cost at least the stated minimum.  Together with `(I1)` this proves the
formula and the optimal-certificate statement.
