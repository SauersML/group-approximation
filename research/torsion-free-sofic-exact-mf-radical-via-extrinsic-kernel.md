---
rg: 2
id: torsion-free-sofic-exact-mf-radical-via-extrinsic-kernel
kind: route
title: Realize the exact radical directly as an extrinsic mapping-torus defect
target: torsion-free-sofic-exact-mf-radical-over-z
requires:
  - torsion-free-sofic-extrinsic-kazhdan-defect-kernel
  - split-cyclic-kazhdan-defect-exact-mf-radical
  - finitely-generated-rf-automorphism-mapping-torus-is-rf
  - finite-outer-order-mapping-torus-is-virtually-product
---

Choose `K,phi,L` satisfying `(EK1)`, including finite presentation of its
mapping torus, and put

```text
G = K semidirectProduct_phi Z.
```

The hypotheses are exactly those of
`split-cyclic-kazhdan-defect-exact-mf-radical`, which gives

```text
Rad_MF(G)=K x {0},     G/Rad_MF(G) ~= Z,
```

together with finite presentation, torsion-freeness, soficity,
hyperlinearity and non-MF.  Its universal factorization statement identifies
all homomorphisms from `G` to countable MF groups with those from `Z`.

If the preferred normal generator is supplied, it also normally generates
the radical in `G`.  Unlike the direct-product defect-core route, this route
does not require `K` to have full MF radical in isolation.
