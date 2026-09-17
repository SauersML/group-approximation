---
rg: 2
id: symbol-blind-bijectivity-gives-defect-counting-identities
kind: route
title: Bijectivity at every alphabet gives the counting identities by measure preservation
target: symbol-blind-defect-counting-identities
requires:
  - symbol-blind-injective-automata-are-bijective
  - symbol-blind-automata-reduce-to-defect-counting
---

Assume tau_q is injective for every q.

1. By symbol-blind-injective-automata-are-bijective, tau_q is bijective for
   every q.
2. By bijective-ca-preserve-uniform-bernoulli-measure, tau_q preserves mu_q for
   every q. This dependency is already a prerequisite of the reduction node.
3. By part 4 of symbol-blind-automata-reduce-to-defect-counting, (b) implies
   (c): N_j^T = N_j^{id} for every j.

So the identities and the bijectivity claim are equivalent. Over sofic groups
Gottschalk's conjecture is a theorem, so the identities of every order hold
there. A proof of the identities that does not separate sofic from nonsofic
groups settles the symbol-blind class everywhere.
