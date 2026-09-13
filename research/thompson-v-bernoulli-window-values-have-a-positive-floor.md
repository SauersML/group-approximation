---
rg: 2
id: thompson-v-bernoulli-window-values-have-a-positive-floor
kind: claim
title: Bernoulli window values over Thompson's V have a uniform positive floor
refuted_by:
  - thompson-v-nonsurjunctive
distinct_from:
  thompson-v-has-positive-rokhlin-entropy-action: that asks for one free ergodic action of V with positive Rokhlin entropy; this is the finitary lower bound a model-free proof must establish, equivalent to it through bernoulli-per-copy-rokhlin-entropy-is-zero-or-full and the self-copy dichotomy.
  rokhlin-window-transport-is-dominated: that is a transport bound with constant 1 over every group; this is a floor with any positive constant over V alone.
  thompson-v-is-sofic: that would give this claim through sofic entropy; this could hold with V nonsofic.
artifacts:
  - research/artifacts/rokhlin-supremum-dichotomy-on-leavitt-units-and-v-2026-09-12.md
---

**OPEN.** Let `V = G_(2,1)`. There are `q >= 2` and `c > 0` such that every configuration `(k, E, F, psi)` over `V` at
alphabet size `q` has `Phi(k, E, F, psi) >= c`, in the sense of `bernoulli-rokhlin-deficit-has-a-finitary-witness`.

**Why this is the missing inequality.** This is Section 6.1 of the artifact.

- By `bernoulli-per-copy-rokhlin-entropy-is-zero-or-full`, `inf Phi` over `V` is `0` or `log q`. So a floor with any
  `c > 0` is already maximality at every alphabet, and no weaker constant is a weaker target.
- The negation is one finite configuration over `V` with `Phi < log q`. Its incidence pattern is decidable through the
  word problem of the binary Leavitt unit group, which contains `V`.
- The positive side is cheapest here. INF of the Leavitt unit group gives this claim, and `thompson-v-is-sofic` gives
  it through sofic entropy.

**Payoff.**

- It gives `thompson-v-has-positive-rokhlin-entropy-action` (route `thompson-v-positive-rokhlin-from-window-floor`).
- It then gives quantitative surjunctivity of `V` (`maximal-bernoulli-rokhlin-entropy-makes-groups-uqs`), surjunctivity
  of `V`, and direct finiteness of `K[V]`.
- A nonsurjunctive `V` has a strict automaton, which gives a deficit configuration
  (`strict-automaton-lowers-bernoulli-rokhlin-entropy`) and refutes this claim.

## Attempts

- **Where each known inequality points (w7-rokhlin-dichotomy, 2026-09-12).** None of these gives a floor. This is
  Section 4 of the artifact.
  - Restriction to sofic or amenable subgroups bounds from above.
  - Co-amenable ascent is available over `V` only through a sofic co-amenable subgroup.
  - The compressions `V_[0] <= V` have infinite index.
  - Theorem A spreading creates no lower bound, and Corollary A1 holds on INF and non-INF hosts alike (Proposition 3.1).
  - Koopman data, weak containment, cost and ℓ²-Betti numbers do not depend on the base.
  - The codeword Følner count loses `lambda(F)`, which is unbounded over `V ⊇ F_2 x F_2`.
