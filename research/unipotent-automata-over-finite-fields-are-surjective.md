---
rg: 2
id: unipotent-automata-over-finite-fields-are-surjective
kind: claim
title: Injective automata of the form identity plus higher-order terms over F_q are surjective over every group
distinct_from:
  sofic-groups-are-surjunctive: that proves every automaton surjective on sofic hosts; this proves one normal-form class surjective on every host, under a degree bound on the decoder.
  gottschalk-surjunctivity-conjecture: that is every automaton on every host; this is only automata with invertible linear part and a low-degree decoder, and it says nothing about decoders of degree product at least q.
artifacts:
  - research/artifacts/low-degree-strict-pairs-linear-parts-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `F = F_q` and let `G` be any group. Let `tau` be an automaton over `F^m` with `tau(0) = 0`
whose linear part `tau_A` is a bijective linear automaton; for example `tau = id + N` with every
monomial of `N` of degree at least 2. If `tau` has a left inverse `sigma` with
`deg sigma * deg tau < q`, then `tau sigma = id`, so `tau` is surjective.

**Proof idea** (Theorem 7 of the artifact).

- *The formal ring.* Work in `P = F[x_u : u in G]`, with no reduction `x^q = x`. The degree bound
  makes formal and functional composites agree, so `tau^* sigma^* = id_P` and `tau^*` is onto.
- *Injectivity.* The lowest homogeneous part of `tau^*(f)` is `tau_A^*(f_j) != 0`, so `tau^*` is
  injective.
- *Conclusion.* `sigma^* tau^* = id`, which is `tau sigma = id`.

The infinite variable set is where strictness can hide in general. The invertible linear part
recovers injectivity with no Noetherian input.

**Scope.** On `F_8`, the pair `x^3`, `y^5` is bijective with zero linear part and degree
product `15 >= 8`. The bound is needed for Step 1, and the invertible linear part for Step 2.

Established 2026-09-12 by `unipotent-automata-over-finite-fields-are-surjective-proof`. The
first dead attempts (measure marginals, the scaling torus, iterative solving) are recorded in
Section 6 of the artifact.
