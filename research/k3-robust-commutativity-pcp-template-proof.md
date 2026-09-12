---
rg: 2
id: k3-robust-commutativity-pcp-template-proof
kind: route
title: Use exceptional three-colouring to close the robust PCP-template choice
target: pcp-template-with-robust-quantum-commutativity
requires:
  - simple-algebraic-pcp-binary-local-test
  - quantum-polymorphism-commutativity-gadget
  - mastel-slofstra-private-context-augmentation-preserves-defect
---

Choose `K_3=C_3`.  Graph 3-colouring is NP-complete.  Culf--van Dobben de
Bruyn--Zeman compute
`Mor^+(K_3^k,K_3) = (S_3^+)^{disjoint union k}`; the exceptional identity
`S_3^+=S_3` makes all these polymorphisms classical.  Their bounded-arity
characterization and exact-to-robust theorem therefore give `K_3` a `qa`
commutativity gadget and a robust finite-dimensional one.

The binary PCP has a fixed finite menu of constant-query Boolean predicates.
Apply the ordinary Boolean-CSP-to-3-colouring reduction separately to each
check.  Each gadget has bounded size: a satisfied check extends exactly, while
a false check leaves at least one of a bounded number of edges unsatisfied.
Thus the weighted loss is one fixed constant.  Keep original proof vertices
shared and make every new gadget vertex private using the Mastel--Slofstra
context-augmentation theorem.  Install commutativity gadgets for all PVM pairs
used by the local joint-assignment argument.  This proves the relational
template statement, but not its later scalar-group-word compilation.
