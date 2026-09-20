---
rg: 2
id: exact-mf-radical-over-z-via-locally-mf-stable-kernel
kind: route
title: Take the mapping torus of a quotientless sofic Kazhdan kernel that is locally MF-stable in operator norm, along an automorphism with a finite automorphic presentation
target: torsion-free-sofic-exact-mf-radical-over-z
requires:
  - torsion-free-sofic-quotientless-locally-mf-stable-kazhdan-kernel
  - locally-mf-stable-kazhdan-kernels-collapse-torus-radicals
  - fp-mapping-torus-iff-finite-automorphic-presentation
  - sofic-kernel-amenable-quotient-permanence
---

This route contains `exact-mf-radical-over-z-via-automorphic-full-radical-kernel`: its hole implies
this one, because `Rad_MF(K) = K` gives (Q) and (LS). It also admits MF, and then LEF, kernels.

Take `K`, `φ` as in `torsion-free-sofic-quotientless-locally-mf-stable-kazhdan-kernel`, and put
`G = K ⋊_φ Z`. Check the clauses of `(TFZ1)` for `(G, K)`.

- **Finitely presented.** By (P2) and the "if" direction of
  `fp-mapping-torus-iff-finite-automorphic-presentation`.
- **Torsion-free.** An element of finite order maps to `0` in `G/K = Z`, so it lies in `K`, which is
  torsion-free by (P1').
- **Sofic.** `K` is sofic and `Z` is amenable, so `G` is sofic by
  `sofic-kernel-amenable-quotient-permanence`.
- **Kernel.** `K` is nontrivial, normal and Kazhdan by (P1').
- **`Rad_MF(G) = K`.** `G` is finitely presented, `K` is Kazhdan and locally MF-stable, and `K` has no
  nontrivial finite quotient. That is exactly the hypothesis of Corollary D3 of
  `locally-mf-stable-kazhdan-kernels-collapse-torus-radicals`, which gives `Rad_MF(G) = K`.
- **`G/K ≅ Z`.** By construction.

So `(G, K)` satisfies `(TFZ1)`.
