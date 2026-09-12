---
rg: 2
id: finitely-generated-rf-automorphism-mapping-torus-is-rf
kind: claim
title: An automorphism mapping torus of a finitely generated residually finite group is residually finite
distinct_from:
  mf-not-closed-under-integer-extensions: That exhibits a split integer extension of an MF kernel which is non-MF; residual finiteness of the kernel is the extra hypothesis that rules this out here.
  periodic-higman-mapping-torus-is-word-hyperbolic: That treats mapping tori of a particular injective free-group endomorphism; this is the general automorphism theorem and uses characteristic finite quotients.
---

Let `K` be finitely generated and residually finite and let `phi` be an
automorphism of `K`.  Then

```text
G = K semidirectProduct_phi Z
```

is residually finite.  Consequently `G` is MF and
`Rad_MF(G)={1}`.

In particular, no split-cyclic construction with a nontrivial exact MF
radical equal to its kernel can use a finitely generated residually finite
kernel.  A solution of `torsion-free-sofic-exact-mf-radical-over-z` must use
a sofic but non-residually-finite property-`(T)` kernel.
