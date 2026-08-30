---
rg: 2
id: stw95-nuclear-successor-filtrations-need-no-exact-factor
kind: claim
title: Nuclear successor layers reduce tensor purity without exactness of the other factor
artifacts:
  - research/artifacts/stw95-pure-tensor-permanence-wave-audit-2026-08-30.md
distinct_from:
  stw95-transfinite-exact-filtration-reduction: that allows arbitrary successor layers but assumes the tensor factor is exact; this assumes nuclear successor layers and permits an arbitrary tensor factor.
  stw95-transfinite-ash-layered-factor-preserves-purity: that is a concrete positive class obtained from the Seth--Vilalta theorem; this is the general local-to-global reduction and applies whenever the layer products are pure.
  stw95-af-factor-preserves-purity: that treats an AF tensor factor itself; the corollary here permits a separable factor assembled by arbitrary continuous extensions of AF layers and does not assert that the resulting factor is AF.
---

Let `A` be any C*-algebra.  Let `B` be separable and admit a continuous
increasing filtration `(J_alpha)_(alpha<=gamma)` by closed ideals, indexed by
an arbitrary ordinal, with

```text
J_0=0,                 J_gamma=B,
J_lambda=closure(union_(alpha<lambda) J_alpha)
```

at every limit ordinal.  Put

```text
L_alpha=J_(alpha+1)/J_alpha.
```

If every `L_alpha` is nuclear and every `A tensor_min L_alpha` is pure, then

```text
A tensor_min B
```

is pure.  No exactness or separability assumption is imposed on `A`.

Thus nuclearity of the filtration cells is a second, genuinely asymmetric
way to cross the tensor-exactness bottleneck: it makes every successor
extension semisplit, whereas
`stw95-transfinite-exact-filtration-reduction` instead exacts the whole
filtration by assuming `A` exact.

In particular, if `A` is pure and every `L_alpha` is AF, then
`A tensor_min B` is pure.  Hence, if `B` is pure as well, every such pair is
a positive class for Problem XCV.  This AF-layered corollary imposes no
exactness, separability, simplicity, or quotient condition on `A`; its AF
layers need not be unital, and `B` need not itself be AF.
