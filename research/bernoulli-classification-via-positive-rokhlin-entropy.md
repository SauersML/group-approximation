---
rg: 2
id: bernoulli-classification-via-positive-rokhlin-entropy
kind: route
title: Positive Rokhlin entropy over every group makes Rokhlin entropy separate Bernoulli shifts by base entropy
target: bernoulli-shift-entropy-classifies-for-every-group
requires:
  - every-group-has-positive-rokhlin-entropy-action
  - seward-per-group-rokhlin-entropy-of-bernoulli-shifts
---

Assume that every countably infinite group has a free ergodic p.m.p. action of
positive Rokhlin entropy, and fix a countably infinite group `G`. "Item n" refers
to `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`.

1. **INF(G).** Suppose `h_sup(G) < ∞`. Item 3, applied with
   `P = ⊕_n Z/nZ` (which has arbitrarily large finite subgroups), gives
   `h_sup(P × G) = 0`. That contradicts the hypothesis for `P × G`. So
   `h_sup(G) = ∞`.
2. **RBS(G).** For finite `H(L,lambda)`, item 1 gives
   `h^Rok_G(L^G,lambda^G) = H(L,lambda)`. For infinite `H(L,lambda)`, item 2 gives
   `∞`, since INF(G) provides a positive-entropy action.
3. **INV(G).** Rokhlin entropy is an isomorphism invariant, so bases of different
   entropy give non-isomorphic Bernoulli shifts.

**Scope.** The hypothesis is used for the auxiliary group `P × G`, not only for `G`.
For one group, it suffices to have INF(G). For one pair of finite base entropies
`h_1 < h_2`, the weaker `h_sup(G) > h_1` suffices, by item 1. Seward records that
POS(G) ⇒ INF(G) is unknown for a single group.

The necessary conditions on a counterexample group are
`bernoulli-entropy-counterexample-constraints`.
