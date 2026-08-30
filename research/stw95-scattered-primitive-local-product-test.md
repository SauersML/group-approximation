---
rg: 2
id: stw95-scattered-primitive-local-product-test
kind: claim
title: Tensor purity over a scattered primitive spectrum is detected on simple subquotients
distinct_from:
  stw95-nuclear-successor-filtrations-need-no-exact-factor: that theorem starts with a specified ordinal filtration; the present theorem extracts the required filtration intrinsically from the topology of the primitive spectrum.
  stw95-transfinite-ash-layered-factor-preserves-purity: that theorem assumes a displayed ASH-layer filtration; here no filtration is part of the input, and the general criterion only asks for nuclearity and product purity of simple subquotients.
  stw72-scattered-primitive-spectrum-wpi-is-purely-infinite: that theorem uses the same topological peeling to propagate pure infiniteness within one algebra; this theorem propagates purity of a minimal tensor product and does not assume either factor is weakly purely infinite.
artifacts:
  - research/artifacts/stw95-scattered-primitive-tensor-localization-audit-2026-08-30.md
---

Let `A` be any C*-algebra and let `B` be separable with topologically
scattered primitive spectrum.  Suppose that, for every nonzero simple
subquotient `L` of `B`,

```text
L is nuclear,                 A tensor_min L is pure.   (SPT1)
```

Then

```text
A tensor_min B is pure.                              (SPT2)
```

No exactness, separability, simplicity, or purity assumption is imposed on
`A`.  The statement is intrinsic: no composition series for `B` is part of
the hypotheses.

In particular, let `A` be pure and assume either that `A` is simple or that
every quotient of `A` is stably finite.  If every simple subquotient of `B`
is ASH, then `(SPT2)` holds.  Consequently, when `B` is also pure, this is a
positive class for the general tensor-permanence part of Problem XCV.  The
algebra `B` need not itself be ASH or Z-stable; it may have an ordinal ideal
filtration of arbitrary height.
