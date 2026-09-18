---
rg: 2
id: defect-counting-identities-give-symbol-blind-bijectivity
kind: route
title: Counting identities of every order give bijectivity by closed image and full support
target: symbol-blind-injective-automata-are-bijective
requires:
  - symbol-blind-defect-counting-identities
  - symbol-blind-automata-reduce-to-defect-counting
---

Assume tau_q is injective for every q.

1. By symbol-blind-automata-reduce-to-defect-counting part 5, N_0^T = N_0^{id}
   and N_1^T = N_1^{id}.
2. By symbol-blind-defect-counting-identities, N_j^T = N_j^{id} for j >= 2.
3. By part 4 of the same node, (c) implies (b): tau_q preserves the uniform
   Bernoulli measure mu_q for every q.
4. Fix q. The image tau_q([q]^G) is closed, being a continuous image of a
   compact space. It has mu_q-measure 1. Every nonempty open set has positive
   mu_q-measure, so the complement of the image, which is open and null, is
   empty. So tau_q is surjective.
