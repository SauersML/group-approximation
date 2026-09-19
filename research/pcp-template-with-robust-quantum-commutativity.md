---
rg: 2
id: pcp-template-with-robust-quantum-commutativity
kind: claim
title: Choose an NP-hard binary PCP template with a qa commutativity gadget and bounded-loss reductions
distinct_from:
  quantum-polymorphism-commutativity-gadget: that characterizes and robustifies a gadget once the finite template is fixed; this must exhibit a template which also receives the algebraic PCP checks with bounded weighted defect.
  mastel-slofstra-private-context-augmentation-preserves-defect: that preserves defect under a supplied contextwise classical transformation; this must supply the source and target relational templates and the required transformations.
---

Take `A = K_3 = C_3`.  Then:

1. `CSP(K_3)` is graph 3-colouring and is NP-complete;
2. the complete-graph decomposition
   `Mor^+(K_3^k,K_3) = (S_3^+)^{disjoint union k}`, together with
   `S_3^+ = S_3`, makes every quantum polymorphism classical, so
   `quantum-polymorphism-commutativity-gadget` gives a `qa` gadget and a
   robust finite-dimensional gadget;
3. every check of the fixed constant-query verifier in
   `simple-algebraic-pcp-binary-local-test` has a bounded-size classical
   reduction to 3-colouring.  A false check leaves at least one edge of that
   bounded gadget unsatisfied, so the weighted soundness loss is a constant;
4. private auxiliary vertices are installed contextwise using
   `mastel-slofstra-private-context-augmentation-preserves-defect`, while the
   original proof coordinates remain shared.

This establishes the relational/weighted template.  It does **not** establish
`k3-relational-atlas-to-scalar-group-words`: projection-valued 3-colouring
constraints and robust local commutation are not yet scalar group relators or
the diagonal/crossed endpoint comparisons of the S3 radical charts.

## Audit obligations

- Use one common reference triangle inside each bounded local reduction, and
  keep its auxiliary vertices private to that context.
- Pairwise commutativity gadgets must cover every pair of PVMs whose joint
  classical assignment is used in the local soundness argument.
- Do not infer global commutation between proof coordinates occurring in
  different contexts.
