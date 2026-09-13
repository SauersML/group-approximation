---
rg: 2
id: fpbs-pivotal-kernels-hold-on-known-gap-test-graphs
kind: claim
title: Regular trees, hyperbolic groups and tree-by-lattice products satisfy all four pivotal kernels
distinct_from:
  fpbs-hyperbolic-and-nonunimodular-nonuniqueness: that is p_c<p_u on these classes; this verifies the four pivotal kernel estimates on them, testing the kernels where the conjecture is already known.
  fpbs-cactus-finite-ball-pivotal-budget: that proves the budget on cacti through their cycle structure; most graphs here are not cacti.
  fpbs-l2-gap-cayley-graphs-satisfy-pivotal-kernels: that proves the kernels under the hypothesis p_c<p_(2->2); this names concrete families of test graphs and checks the hypothesis on them.
---

Section 5 of
`research/artifacts/fpbs/docs/pivotal-kernel-ordering-2026-09-12.md`.

Each Cayley graph below satisfies `fpbs-pivotal-budget-universal`, with a count
bounded independently of `n`. It also satisfies:

* `fpbs-integrated-sensitivity-universal`;
* `fpbs-pivotal-nonconcentration-universal`;
* `fpbs-universal-subcritical-pivotal-growth-rate`.

The graphs:

* `T_k = Cay((Z/2)^(*k))` with `k>=3`;
* `Cay(Gamma,S)`, for a nonelementary hyperbolic group `Gamma` and any finite
  symmetric generating set `S`;
* `T_k x Z^m = Cay((Z/2)^(*k) x Z^m)`, with the product generators, `k>=3` and
  `m>=1`. Its automorphism group contains the transitive nonunimodular
  subgroup `Aut_xi(T_k) x Z^m`.

`p_c<p_u` is already known on each of these graphs. The kernels were tested
there for obstructions, and none fails, so no obstruction is recorded. For
`m>=1` the third family is neither hyperbolic nor a cactus.
