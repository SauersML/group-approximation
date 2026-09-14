---
rg: 2
id: infinite-symmetric-groups-miss-a-unimodular-root-proof
kind: route
title: Conjugacy to a transposition forces the root to be a transposition, and the five remaining cases fail
target: infinite-symmetric-groups-miss-a-unimodular-root
requires: []
---

Elementary. Products are compositions, `(gh)(i) = g(h(i))`. For `g in Sym(Omega)`
and distinct `i, j`, the conjugation formula is `g (i j) g^(-1) = (g(i) g(j))`.

## Item 1: `x a x a x^(-1) b = 1` has no root

Suppose `x in Sym(Omega)` satisfies `x a x a x^(-1) b = 1`, with `a = (0 1)`
and `b = (0 2)`.

1. **Rewrite.** Multiplying on the right by `b^(-1) = b` gives
   `x (a x a) x^(-1) = b`. So `a x a` is conjugate to the transposition `b`,
   hence is a transposition, and `x = a (a x a) a` is a transposition too.
   Write `x = (i j)` with `i != j`, and put `A = {i, j}`.
2. **The condition.** Since `x = x^(-1)`, the relation says
   `a x a = x b x`. By the conjugation formula this reads
   `{a(i), a(j)} = {x(0), x(2)}`, i.e. `a(A) = x({0, 2})`.
3. **Cases**, according to how `A` meets `{0, 2}`:
   - **`A` disjoint from `{0, 2}`.** Then `x({0,2}) = {0,2}`, so
     `A = a({0,2}) = {1,2}`, which contains `2`. Contradiction.
   - **`A = {0, 2}`.** Then `x({0,2}) = {0,2}`, but `a(A) = {1,2}`.
     Contradiction.
   - **`A = {0, k}` with `k != 2`.** Then `x({0,2}) = {k, 2}` and
     `a(A) = {1, a(k)}`. Equality needs `1 in {k, 2}`, so `k = 1`, and then
     `a(k) = 0` must equal `2`. Contradiction.
   - **`A = {2, k}` with `k != 0`.** Then `x({0,2}) = {0, k}` and
     `a(A) = {2, a(k)}`. Equality needs `2 in {0, k}`, so `k = 2`, but
     `k != 2` because `A` has two elements. Contradiction.

So there is no root. The word has exponent sum `1 + 1 - 1 = 1`. Nothing above
depends on the size of `Omega` beyond containing `0, 1, 2`.

## Item 2: a transposition is not a square

Let `t in Sym(Omega)`. On a finite cycle of `t` of length `k >= 3`, or on an
infinite orbit, `t^2` moves every point, so it moves at least three points
there. On cycles of length `1` or `2`, `t^2` is the identity. If `t^2 = (0 1)`,
which moves exactly two points, then every cycle of `t` has length at most
`2`. Hence `t^2 = 1`, a contradiction.

## Consistency check against the conjecture

The coefficients of item 1 generate `S_3`, and those of item 2 generate `C_2`.
By `kervaire-laudenbach-holds-for-hyperlinear` both equations have roots in
overgroups. Concretely:
- item 2 is solved by a 4-cycle once `(0 1)` is represented diagonally on two
  copies of `Omega`;
- item 1 is solved inside some unitary group by Gerstenhaber--Rothaus, as
  recorded on that node.

The failure is of internal solvability only.
