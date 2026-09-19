---
rg: 2
id: finite-outer-order-mapping-torus-is-virtually-product
kind: claim
title: A mapping torus of finite outer order is virtually a direct product
distinct_from:
  finitely-generated-rf-automorphism-mapping-torus-is-rf: That uses residual finiteness of the kernel for every automorphism; this uses finite order in the outer automorphism group and needs no finiteness or residual hypothesis on the kernel.
  mf-is-commensurability-invariant: That supplies the MF consequence after the finite-index product subgroup is identified; this identifies that subgroup.
---

Let `phi in Aut(K)`.  If the class of `phi` has finite order in `Out(K)`,
then the mapping torus

```text
G = K semidirectProduct_phi Z
```

has a finite-index subgroup isomorphic to `K x Z`.

Consequently, if `K` is MF, then `G` is MF.  Thus a non-MF automorphism
mapping torus must satisfy at least one of the following:

```text
K is already non-MF;
[phi] has infinite order in Out(K).                       (FO1)
```

For a simple non-MF kernel the first alternative automatically gives full MF
radical in `K`; the genuinely extrinsic route therefore needs an
infinite-order outer automorphism.
