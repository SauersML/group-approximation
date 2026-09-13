---
rg: 2
id: induced-cantor-action-type-semigroup-matches-subgroup
kind: claim
title: Inducing a Cantor action from a finite-index subgroup keeps freeness, minimality and the type semigroup
---

Let `G` be a countable group, `H <= G` a subgroup of finite index `k`, and
`H` act on a Cantor space `X`.  Let `Y = G x_H X` be the induced space, the
quotient of `G x X` by `h.(g, x) = (g h^(-1), h x)`, with `G` acting by left
multiplication on the first coordinate.  Then:
* `Y` is a Cantor space, homeomorphic to `k` disjoint copies of `X`;
* the `G`-action on `Y` is free if and only if the `H`-action on `X` is free;
* it is minimal if and only if the `H`-action is minimal;
* `[A] -> [ {e} x A ]` is a monoid isomorphism
  `S(X, H) -> S(Y, G)` with `[1_Y] -> k [1_X]`.

In particular `S(Y, G)` is almost unperforated if and only if `S(X, H)` is,
and `G`-invariant probability measures on `Y` correspond to `H`-invariant
ones on `X`.

**Use.**  Every free group `F_n` with `2 <= n < infinity` is a subgroup of
index `n - 1` in `F_2`.  So a free minimal Cantor action of some `F_n`, `n`
finite, whose type semigroup is not almost unperforated gives one for `F_2`
(`rainone-f2-question-via-finite-rank-free-subgroup`).  The group `F_inf` of
the Boldrini--Prasad examples has infinite index in `F_2`, so this lemma does
not reach them.
