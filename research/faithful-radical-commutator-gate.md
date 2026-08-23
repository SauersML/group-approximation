---
rg: 2
id: faithful-radical-commutator-gate
kind: claim
title: One free-product commutator faithfully gates an arbitrary word problem into any homomorphism-monotone radical
artifacts:
  - GroupApproximation/Algebra/FaithfulRadicalCocycle.lean
distinct_from:
  mf-radical-functoriality: that only transports an already invisible element; this combines transport with free-product normal form to detect every control element exactly and injectively.
  marked-mf-radical-seed-gives-proof-triggered-compiler: that changes a presentation after a machine halts; this uses one fixed free product and lets only the control word vary.
---

Let `R` assign a normal subgroup `R(G)` to every group, functorially under
homomorphisms.  If `1 != z in R(H)`, then in `H * B` the pointed map

```text
delta_z(b) = [inl(z), inr(b)]
```

has all of the following properties:

* `delta_z(b) in R(H * B)`;
* `delta_z(b)=1` iff `b=1`;
* `delta_z` is injective;
* `delta_z(b)` lies in `[R(H * B), H * B]`;
* it is natural in homomorphisms out of `B`;
* it obeys the nonabelian cocycle identity
  `delta_z(bc)=delta_z(b) b delta_z(c) b^-1`.

The radical statement uses only functoriality and normality.  Faithfulness is
the reduced alternating word of length four in the free product.  The complete
algebraic package is formalized in
`GroupApproximation/Algebra/FaithfulRadicalCocycle.lean`.
