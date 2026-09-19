---
rg: 2
id: two-matching-block-propagation-closes-metapixel
kind: route
title: Use two field matchings as the sparse twisted-commutation sampler
target: bounded-degree-entangled-agreement-pauli-metapixel
requires:
  - two-matching-matrix-block-propagation
  - two-matchings-force-exponential-dimension-with-multiplicity
  - two-untwisted-field-matchings-force-complete-cross-commutation
---

Use the two matchings `a=b` and `a=A b` for the mixed component.  Their
degree is two and their exact phase pattern has perfect Weyl completeness.
The first prerequisite supplies uniform soundness for arbitrary decoded
same-basis multiplicities; the other two record that the exact abstract
group and the exact twisted Weyl table are already completely rigid.  Combine
this sampler with a finite-template robust same-basis
linearity/agreement code and choose/delete the negligible short matching
cycles before relative graphical labeling.  This yields the metapixel
clauses without a complete mixed table.
