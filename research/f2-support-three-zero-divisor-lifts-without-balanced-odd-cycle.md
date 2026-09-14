---
rg: 2
id: f2-support-three-zero-divisor-lifts-without-balanced-odd-cycle
kind: claim
title: An F_2 support-three zero divisor whose Kaplansky graph has no balanced odd cycle lifts to a complex zero divisor with the same supports
distinct_from:
  kaplansky-zero-divisor-conjecture: that is the conjecture over every field; this transfers a characteristic-two counterexample of support three to characteristic zero under a condition on its Kaplansky graph.
  zero-divisor-support-vertex-cones-contain-positive-relations: that derives positive relations from any zero divisor; this constructs a characteristic-zero zero divisor from an F_2 one.
  f2-support-three-zero-divisors-need-support-at-least-22: that bounds the support of the cofactor by search; this is a structural transfer that applies at every support size.
---

**ESTABLISHED.** Let `G` be a group, `x, y in G` with `1, x, y` distinct,
`alpha = 1 + x + y in F_2[G]`, and `beta = 1_B` for a finite nonempty `B` with
`alpha beta = 0`.

1. *Kaplansky graph.* Every `s in G` has either no or exactly two expressions
   `s = c b` with `c in {1, x, y}`, `b in B`. The graph `K` has vertex set `B`
   and one edge for each `s` with two expressions `s = c b = c' b'`.
   Traversing that edge from `b` to `b'` reads the letter `u = c'^-1 c`, a
   formal letter among `X^(+-1), Y^(+-1), (X^-1 Y)^(+-1)` in the free group
   `F(X, Y)`, and `b' = u b` in `G`.
2. *Balance.* Each oriented edge carries `e(u) in Z^2`, the exponent sums of
   `X` and `Y` in its letter, and length `1`. This defines homomorphisms
   `e: H_1(K; Z) -> Z^2` and `pi: H_1(K; Z) -> Z/2` (length parity). Call an
   integral 1-cycle `z` of `K` *balanced odd* if `e(z) = 0` and `pi(z) = 1`.
   When `K` is connected, a balanced odd cycle is represented by a closed walk
   reading a word with zero exponent sums and odd length.
3. *Lift.* Suppose `K` has no balanced odd cycle. Then for every algebraically
   closed field `k` of characteristic `!= 2` there are `s, t in k^*` and
   `w: B -> k^*` with

   ```text
   (1 + s x + t y) * sum_(b in B) w(b) b = 0   in k[G].
   ```

   So `k[G]` has a zero divisor with the same supports `{1, x, y}` and `B`.

**Corollary.** If `k[G]` has no zero divisors for some algebraically closed `k`
of characteristic `!= 2`, then the Kaplansky graph of every F_2 support-three
zero divisor in `F_2[G]` has a balanced odd cycle, and so it is not bipartite.
This applies for instance with `k = C` to torsion-free groups for which `C[G]`
is known to be a domain, such as those satisfying the Strong Atiyah
conjecture.

*Scope.* Elementary; no novelty is claimed. Check: for `G = Z/3 = <g>`,
`alpha = 1 + g + g^2`, `beta = 1 + g`, the graph `K` has two vertices and
three parallel edges, and the lift is `1 + omega g + omega^2 g^2` with
`omega^3 = 1`.

DERIVATION
[[f2-support-three-characteristic-zero-lift-proof]]
