---
rg: 2
id: amenable-quotient-preserves-metric-approximability
kind: claim
title: Amenable quotients preserve four metric approximation classes
distinct_from:
  sofic-semidirect-product-closure-fails: that refutes closure for arbitrary sofic kernels and quotients; this theorem imposes amenability on the quotient, not on the kernel.
  ascending-hnn-cannot-create-nonhyperlinearity: that treats one hyperlinear mapping-torus class; this treats arbitrary extensions and all four metric classes.
  weakly-sofic-not-sofic: that separates two approximation classes; this is a permanence theorem internal to each class.
---

Let

```text
1 -> N -> G -> A -> 1
```

be an exact sequence of groups with `A` amenable. For each of the following
properties, independently,

```text
weakly sofic,
sofic,
K-linear sofic (for any fixed field K),
hyperlinear,
```

if `N` has the property, then `G` has the same property.

The direction of the hypothesis is essential. An amenable normal subgroup
with merely sofic quotient does not suffice: the established Kun--Thom
nonsofic wreath products have abelian kernel and residually finite quotient.

**ESTABLISHED 2026-08-31** by
[[brude-sasyk-amenable-quotient-permanence]].
