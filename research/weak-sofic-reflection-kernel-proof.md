---
rg: 2
id: weak-sofic-reflection-kernel-proof
kind: route
title: Glebsky--Rivera's closure criterion closes bounded products of relator conjugates and nothing larger
target: weak-sofic-reflection-kernel-is-bounded-width-closure
requires:
  - glebsky-rivera-w-sofic-criterion
artifacts:
  - research/artifacts/metric-ultraproduct-bounded-width-closure-2026-09-12.md
---

Artifact, Lemma 2.1 and Proposition 2.3.

- **Subgroup.** The profinite topology makes `F` a topological group, so `cl(A) cl(B) ⊆ cl(AB)`. The sets
  `Cons_n^F(R)` are symmetric and conjugation invariant, and `Cons_a · Cons_b ⊆ Cons_(a+b)`.
- **Weakly sofic.** Take `g_j` in `cl(Cons_(n_j)^F(R))`. Each conjugacy class `[g_j]^F` lies in the same closure.
  So their product lies in `cl(Cons_(n_1+...+n_k)^F(R))`, a closed subset of `N_hat`, and the Glebsky–Rivera
  condition holds.
- **Minimal.** `Cons_n^F(R)` is a finite union of products `[r_1]^F ··· [r_k]^F`, with `k <= n` and
  `r_j` in `R^(±1)`. If `F/M` is weakly sofic and `M` contains `R`, the criterion puts each product's closure in
  `M`. A finite union of closures is closed.
