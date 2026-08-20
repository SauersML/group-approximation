---
rg: 2
id: commutativity-gadget-pcp-coordinate-route
kind: route
title: Use robust quantum commutativity gadgets to stabilize the PCP coordinate atlas
target: binary-pcp-coordinate-atlas-in-hs-microstates
requires:
  - simple-algebraic-pcp-binary-local-test
  - quantum-polymorphism-commutativity-gadget
  - pcp-template-with-robust-quantum-commutativity
  - mastel-slofstra-private-context-augmentation-preserves-defect
  - s3-radical-charts-give-linear-local-hs-payment
  - k3-relational-atlas-to-scalar-group-words
---

Reduce every constant-query PCP check to the fixed template from
`pcp-template-with-robust-quantum-commutativity`.  Use the cited exact-to-robust
equivalence to force all commutators required inside a query context with a
dimension-free weighted-defect modulus.  Use contextwise private augmentation
for auxiliary proof symbols, preserve the original shared coordinate words,
and compile the remaining fixed predicates through the S3 local payment
theorem.

This removes the need to hand-round each context's commuting measurement
algebra.  The separate groupification claim is mandatory: without it, this is
only a robust relational CSP reduction and cannot establish the target group
atlas.
