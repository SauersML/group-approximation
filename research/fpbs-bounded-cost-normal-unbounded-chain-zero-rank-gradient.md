---
rg: 2
id: fpbs-bounded-cost-normal-unbounded-chain-zero-rank-gradient
kind: claim
title: Normal chains whose image in the quotient by a bounded-cost normal subgroup has unbounded index have zero rank gradient, and otherwise the gradient is carried by a profinite action of that subgroup
distinct_from:
  fpbs-normal-finite-cost-rankgradient-counterexample-reduction: that is the conditional refutation of fixed price from a positive-gradient chain; this kills that route on every chain with unbounded image in G/N when N has bounded action cost, and bounds the gradient on the remaining chains.
  fpbs-kazhdan-positive-rank-gradient: that concerns Kazhdan groups, where no normal subgroup structure is assumed; this concerns groups with an infinite normal subgroup of bounded action cost.
artifacts:
  - research/artifacts/fpbs/normal-finite-cost-rank-gradient-2026-09-17.md
---

Let `G` be finitely generated and `N ◁ G` infinite, and let `(G_n)` be a descending chain of finite-index normal subgroups with trivial intersection.

* **(Kill.)** Suppose every free action of `N` has cost at most `K`, and `[G:G_nN]` is unbounded. Then `RG(G,(G_n)) = 0` (Corollary 3.1).
* **(Transfer.)** Suppose `[G:G_nN]` stabilises at `a`. Then the free ergodic profinite action of `N` along `(N∩G_n)` has cost at least `1 + a·RG(G,(G_n))` (Proposition 4.2).

**Consequence for route R.** A counterexample through `fpbs-normal-finite-cost-rankgradient-counterexample-reduction` needs one of the following:

* (S1) `N` does not have bounded action cost, so `N` is itself a counterexample;
* (S2) the chain has bounded image in `G/N`, and some ergodic profinite action of `N` costs more than one.

Every other member dies at a single step: Theorem A' makes the boundary action cost one.

For finitely generated `N`, the kill case also follows from the elementary counting in the proof of Abert--Nikolov Proposition 13. The new content is the case of infinitely generated `N` of bounded action cost, where no such counting exists.
