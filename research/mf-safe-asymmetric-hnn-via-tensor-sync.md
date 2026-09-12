---
rg: 2
id: mf-safe-asymmetric-hnn-via-tensor-sync
kind: route
title: Add a finite-CEP graph factor and tensor its swap models with the MF-safe witness
target: mf-safe-asymmetric-hnn-replacement
requires:
  - three-bridge-is-cyclic-fiber-product-with-finite-cep
  - mikhailova-fiber-product-gives-regular-mf-benign-compiler
  - regular-mf-tensor-sync-proves-twisted-rope-mf
  - graph-witness-product-supplies-tensor-sync
  - bidirectional-hnn-bridge-trivial-value-is-residually-finite
---

Use the three-generator bridge, so the positive quotient is the cyclic fiber
product `B3(1)<=F_2 times F_2` with effective finite CEP.  Compile the
recursive kernel by the Mikhailova construction, whose ambient group is a
finite direct product of free groups on every branch, and take its direct
product with the fixed graph witness.  Since every recursive-branch kernel is
contained in the positive kernel, this does not change the subgroup cut out by
the witness.

On `INF`, the Mikhailova factor supplies the regular-MF realization and the
central-HNN closure supplies a regular realization of the first rope group;
the graph factor supplies a separate finite map for each finite quotient of
`B3(1)`.  The tensor-sync theorem makes the unchanged asymmetric final rope
edge regularly operator-MF.  On `FIN`, benignness and Britton's lemma still
embed the bridge group containing `E`.  Thus the asymmetric identification is
MF-safe in exactly the special form required by the compiler.
