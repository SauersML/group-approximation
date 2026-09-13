---
rg: 2
id: fpbs-l2-gap-gives-bounded-pivotal-counts
kind: claim
title: The l2 norm of the connectivity operator bounds conditional random-walk pivotal counts
distinct_from:
  fpbs-nonamenability-bounds-critical-connectivity-operator: that is the conjecture that the critical connectivity operator is bounded; this assumes a finite norm at p, turns it into a pivotal bound, and says nothing about when the norm is finite.
  fpbs-pivotal-budget-universal: that is the universal linear budget with no operator hypothesis; this inequality holds on every Cayley graph and is empty when the operator norm is infinite.
  fpbs-cactus-finite-ball-pivotal-budget: that bounds pivotal counts on cactus graphs through their cycle structure; this bound uses only the operator norm and holds on every Cayley graph.
---

Theorem 4.1 of
`research/artifacts/fpbs/docs/pivotal-kernel-ordering-2026-09-12.md`.

Let `G=Cay(Gamma,S)` be any Cayley graph with `d=|S|` and `p in (0,1)`. Let
`T_p` be the operator on `l2(Gamma)` with kernel
`tau_p(u,v)=P_p(u<->v)`. Let `X_n` be the simple or the lazy random walk,
independent of the percolation. For `R>=n` let:

* `E_(n,R)` be the event that `e` connects to `X_n` inside the ball `B_R`;
* `N_(n,R)` be the number of open edges pivotal for that connection.

Then for all `n>=1` and `R>=n`,

    E_p[N_(n,R) | E_(n,R)] <= 2 d ||T_p||_(2->2)^2.

The bound depends on neither `n` nor `R`. It is empty when `||T_p||` is
infinite. That happens in particular at every parameter with a unique
infinite cluster, where `tau_p >= theta(p)^2 > 0`.
