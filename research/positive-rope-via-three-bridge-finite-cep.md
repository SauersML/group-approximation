---
rg: 2
id: positive-rope-via-three-bridge-finite-cep
kind: route
title: Specialize the benign compiler to the cyclic fiber-product graph witness
target: positive-rope-profinite-edge-synchronization
requires:
  - three-bridge-is-cyclic-fiber-product-with-finite-cep
  - finite-cep-kernel-witness-synchronizes-rope
  - positive-benign-compiler-specializes-to-kernel-witness
---

Use the three-generator bridge, whose positive value has effective finite CEP
inside `F_2 times F_2`.  The specialization claim identifies the positive
benign data with the graph kernel witness, and
`finite-cep-kernel-witness-synchronizes-rope` then supplies the effective
cofinal synchronized quotient family.  On the negative branch the ordinary
benign intersection property and Britton's lemma still embed the bridge
group containing `E`.
