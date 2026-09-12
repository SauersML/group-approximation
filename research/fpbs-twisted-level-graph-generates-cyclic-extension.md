---
rg: 2
id: fpbs-twisted-level-graph-generates-cyclic-extension
kind: claim
title: The transport graphing of a cyclic extension generates exactly when its twisted return graph is connected, and for the Bernoulli shift that graph is twisted level percolation
distinct_from:
  fpbs-quotient-split-actions-have-cost-one: that selects whole N-orbits through an N-invariant factor of the quotient action, which the Bernoulli shift lacks; this uses every return time of the cyclic generator to a small set, needs no invariant factor, and turns generation into connectivity of a random graph on N.
  fpbs-normal-subgroup-bounded-cost-fixed-price-one: that is the open fixed price statement for extensions by bounded-cost normal subgroups; this is an exact generation criterion for one explicit low-cost graphing when the quotient is infinite cyclic.
---

**ESTABLISHED** through `fpbs-twisted-level-graph-generates-cyclic-extension-proof`.

**Setting.**
- `Gamma = N semidirect_phi Z`, with `t` generating `Z` and `t u t^-1 = phi(u)` for `u in N`.
- `S` is a finite symmetric subset of `N` whose `phi`-orbit `union_m phi^m(S)` generates `N`. Any finite generating set of `N` qualifies.
- `Gamma` acts freely p.m.p. on `(X, mu)`, and `A` is a Borel subset of `X`.
- The transport graphing is `Phi_A = {t} union {s|_A : s in S}`. Its cost is at most `1 + |S| mu(A)`.

1. **Criterion.** The *twisted return graph* `G_A` has the points of each `N`-orbit as vertices. For every `m in Z`, `s in S` and `z` with `t^m z in A`, it has an edge `{z, phi^-m(s) z}`. Then `Phi_A` generates `R_Gamma` iff `G_A` is connected on almost every `N`-orbit.
2. **Bernoulli shift.** Let `b_Gamma` act on `[0,1]^Gamma` and set `A = {x : x(e) < delta}`. On the orbit `N x`, a pair `(u, m) in N x Z` is *open* when `t^m (u x) in A`. The open pairs are independent with probability `delta`. So `G_A` is the random graph `T_delta(N, S, phi)`: its vertices are `N`, and it has an edge `{u, phi^-m(s) u}` for every open `(u, m)` and `s in S`. This graph is called *twisted level percolation*.
3. **Consequence.** If `T_delta(N, S, phi)` is almost surely connected for arbitrarily small `delta > 0`, then `C(b_Gamma) = 1`.
4. **Products are recovered.** For `phi = id`, each edge `{u, s u}` is open at some level almost surely, so `T_delta` is the whole Cayley graph. This is Gaboriau's product argument.
5. **Where connectivity must fail.** Take `F_2 = <t, x>` written as `F_infinity semidirect Z`: here `N` is the normal closure of `x`, free on `x_i = t^i x t^-i`, and `S = {x, x^-1}`. Then `T_delta` is a subgraph of the Cayley tree of `N` for the basis `{x_i}`. Each tree edge is kept with probability at most `2 delta < 1`. Infinitely many tree edges depend on pairwise disjoint sets of pairs, so almost surely some edge is missing, and `T_delta` is disconnected. That is consistent with `F_2` having fixed price 2. So connectivity can only come from the relations among the elements `phi^-m(s)`, never from infinitely many levels alone.
