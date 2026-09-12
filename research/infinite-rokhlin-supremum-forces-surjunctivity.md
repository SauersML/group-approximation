---
rg: 2
id: infinite-rokhlin-supremum-forces-surjunctivity
kind: claim
title: An infinite Rokhlin entropy supremum forces maximal Bernoulli entropy, surjunctivity and direct finiteness
distinct_from:
  residually-finite-groups-are-surjunctive: that is the classical periodic-point base case for residually finite groups; this is Seward's ergodic-theoretic criterion, with no approximation hypothesis on the group.
artifacts:
  - research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md
---

Let `G` be a countably infinite group. Let `h^Rok_sup(G)` be the supremum of the Rokhlin entropies of the free ergodic p.m.p. actions of `G` with finite Rokhlin entropy. If `h^Rok_sup(G) = infinity`, then:

1. `h^Rok_G(L^G, lambda^G) = H(L, lambda)` for every standard probability space `(L, lambda)`;
2. `G` is surjunctive: every injective cellular automaton on every finite-alphabet full shift over `G` is surjective;
3. `K[G]` is directly finite for every field `K`.

Source: Seward, arXiv:1501.03367v4. Theorems 6.6 and 7.6 give (1). Corollary 4.1 gives (2) and (3).

This is an import. It proves nothing unconditional about any nonsofic group. For sofic groups `h^Rok_sup = infinity` holds because sofic entropy bounds Rokhlin entropy from below, and no other lower-bound method is known.
