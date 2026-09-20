---
rg: 2
id: stochastic-automaton-sections-do-not-force-injectivity-proof
kind: route
title: Average over the Haar kernel of a line-difference automaton, then use the deterministic retract equivalence for the other side
target: stochastic-automaton-sections-do-not-force-injectivity
requires:
  - surjunctivity-iff-automaton-monoid-directly-finite
artifacts:
  - research/artifacts/stochastic-sections-of-automata-2026-09-20.md
  - experiments/markov-section-2026-09-17/check_markov_section.py
---

Artifact Sections 1–3.

- **Surjective with a compact kernel.** Each left coset `g<s>` is a
  bi-infinite line, so `x_g - x_{gs} = y_g` is solved by telescoping. The
  kernel `K` consists of the configurations constant on these cosets. It is
  a nontrivial compact subgroup, invariant under shifts, whose Haar measure
  is shift invariant.
- **The Markov section.** `T f(y)` is the Haar average of `f` over
  `x_y + K`.
  - Window lemma: a window `W` goes to the finite window spanned by the
    coset segments between points of `W`, so `T` is Feller.
  - `T` is equivariant, positive and unital, with `T sigma^* = 1`.
  - `sigma^* T` is the Haar average over `K`, which sends `[x_1 = 0]` to
    `1/n`.
  - Haar preservation follows from `sigma_* lambda = lambda`, and
    faithfulness from surjectivity of `sigma`.
- **Decoder side.** If `tau^* T = 1`, then `tau^*` is onto, so `tau` is
  injective. Surjunctivity then makes `tau^*` invertible. Conversely, the
  required node gives a CA left inverse `sigma` of an injective `tau`, and
  `T = sigma^*`.
- **Check.** The script verifies (c)–(h) exactly on `Z` (`n = 2, 3, 4`, window
  lengths up to 5) and on a `Z^2` window.
