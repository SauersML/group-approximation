---
rg: 2
id: rokhlin-supremum-dichotomy-with-centralized-self-copies-proof
kind: route
title: Run Seward's product argument along a commuting finite subgroup inside the group
target: rokhlin-supremum-dichotomy-with-centralized-self-copies
requires:
  - positive-rokhlin-entropy-action-gives-positive-supremum
  - infinite-rokhlin-supremum-forces-surjunctivity
artifacts:
  - research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

Complete proof in Section 1 of the artifact. It follows Seward's proof of Theorem 6.7 in arXiv:1501.03367v4 step by step.

* **Reduction.** By Seward's Theorem 6.6 it suffices that one finite-base Bernoulli shift over `Gamma` has zero Rokhlin entropy.
* **Independence.** Let `T` be finite, commuting with `G`, with `T ∩ G = 1`. Then the translates `gT`, `g in G`, are disjoint. So the partition by `T`-orbits of `T`-patterns generates a free `G`-Bernoulli factor.
* **Small factor.** By Seward–Tucker-Drob there is a free factor `Y` with Rokhlin entropy below `eps`. It carries a Borel transversal `M` for the free `T`-action.
* **T-invariant generator.** Spreading the `T`-patterns seen on `M` over their `T`-orbits gives a `T`-invariant partition `xi`. It generates modulo `Y`, and along `G` it generates a free ergodic factor of finite entropy. That entropy is at most `h^Rok_sup(G) < log k`, so Krieger's theorem gives a `k`-piece generator for this factor. Its pieces are `T`-invariant because `G` commutes with `T`.
* **Estimate.** Recording that generator on `M` alone gives a partition `alpha` with `sigma-alg_Gamma(alpha) v F_Y = B(X)`. Sub-additivity then gives `h^Rok(L^Gamma) < eps + H(alpha | F_Y) <= eps + log(k)/|T|`.

The corollary takes `G` and the `T_n` in the two factors of an embedded `Gamma x Gamma`. The two prerequisites supply POS iff `h^Rok_sup > 0`, and INF implies RBS, surjunctivity and direct finiteness.

Independently re-derived 2026-09-12 by gk-verify-pos: PASS (Section 13 of the verification artifact). Independence of the translates uses only `T ∩ G = 1`; commutation is used exactly once, to make the atoms of the `k`-piece generator `T`-invariant.
