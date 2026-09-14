---
rg: 2
id: deficiency-zero-kervaire-failure-filter-proof
kind: route
title: Push the killing failure onto finite quotients and read the homology off the balanced complex
target: deficiency-zero-kervaire-failure-forbids-finite-quotients
requires:
  - kervaire-laudenbach-holds-for-hyperlinear
  - deficiency-zero-kervaire-failure-yields-whitehead-counterexample
---

Notation as in the target: `G = <X | R>` balanced with `|X| = |R| = n`,
`w in G * <t>` of exponent sum `+-1`, `G != 1`, `G_w = 1`.

**Quotients.** Let `p: G -> Q` be surjective. It extends to a surjection
`G * <t> -> Q * <t>` fixing `t`, which sends `<<w>>` onto `<<p(w)>>`. So it
induces a surjection `G_w -> Q_{p(w)}`, and `G_w = 1` forces `Q_{p(w)} = 1`.
The exponent sum of `p(w)` in `t` equals that of `w`, which is `+-1 != 0`.

If `Q != 1` is hyperlinear, `kervaire-laudenbach-holds-for-hyperlinear` makes
`p(w)` solvable in a group containing `Q`. By the universal property, `Q` then
injects into `Q_{p(w)}`, so `Q_{p(w)} != 1`. That is a contradiction. Any
subgroup `Q` of some `U(d)` is hyperlinear: the constant sequence embeds `Q` in
the metric ultraproduct of `U(d)`, and distinct elements stay at a fixed
positive normalized Hilbert--Schmidt distance, so the embedding is injective.
This covers finite groups (left regular representation) and the image of any
finite-dimensional unitary representation, which proves items 3 and 4. In particular `G` has no nontrivial abelian
quotient, since a nontrivial abelian group has a nontrivial finite quotient
(cyclic of prime order, or `Z/2` from `Z`).

**Item 1.** `H_1(G) = Z^n / (rows of the exponent-sum matrix M)`. It is `0`
exactly when `M` is invertible over `Z`, i.e. `det M = +-1`. It must be `0`,
because any nonzero finitely generated abelian group has a nontrivial finite
quotient, which is excluded by item 3.

**Item 2.** `K` has one 0-cell, `n` 1-cells and `n` 2-cells, so its Euler
characteristic is `1`. With `H_1(K) = H_1(G) = 0`, `chi(K) = 1 + rank H_2(K)`, so
`rank H_2(K) = 0`. `H_2(K)` is the kernel of a map from the free abelian group on
the 2-cells, hence free, hence `0`. So `K` is acyclic. For any connected
CW complex `K` with `pi_1(K) = G`, Hopf's exact sequence
`pi_2(K) -> H_2(K) -> H_2(G) -> 0` holds (attach cells of dimension at least 3 to
kill the higher homotopy groups; this does not change `H_1` and can only add to
`H_2`, through the cells attached along `pi_2`). So `H_2(K) = 0` gives
`H_2(G) = 0`, and `G` is superperfect.

**Scope.** Nothing here uses the size of the presentation. Item 3 alone is the
computational filter: one certified finite quotient `Q != 1` of `G` rules out
every `w`, of any length.
