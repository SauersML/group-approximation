---
rg: 2
id: pcp-template-with-robust-quantum-commutativity
kind: claim
title: Choose an NP-hard binary PCP template with a qa commutativity gadget and bounded-loss reductions
distinct_from:
  quantum-polymorphism-commutativity-gadget: that characterizes and robustifies a gadget once the finite template is fixed; this must exhibit a template which also receives the algebraic PCP checks with bounded weighted defect.
  mastel-slofstra-private-context-augmentation-preserves-defect: that preserves defect under a supplied contextwise classical transformation; this must supply the source and target relational templates and the required transformations.
---

Exhibit a fixed finite relational structure `A` such that:

1. `CSP(A)` is NP-hard and the binary verifier of
   `simple-algebraic-pcp-binary-local-test` reduces to `A` with a
   constant weighted soundness loss;
2. `A` admits a `qa` commutativity gadget, equivalently the bounded-arity
   polymorphism condition of
   `quantum-polymorphism-commutativity-gadget`;
3. the reduction preserves exact commuting/tracial completeness and shared
   proof-coordinate identities;
4. all introduced auxiliary variables can be made private without changing
   context intersections.

The complete-graph target cannot simply be assumed: its quantum
polymorphisms contain the nonclassical quantum permutation group `S_n^+`.

## Attempts

- Search among the explicit templates used in robust quantum CSP hardness
  reductions, then verify the `|A|^2` polymorphism condition rather than
  designing a commutativity gadget by hand.
- A template with only a finite-dimensional `q` gadget is insufficient: the
  cited equivalence robustifies a `qa` gadget, not every strictly weaker
  `q`-only gadget.
