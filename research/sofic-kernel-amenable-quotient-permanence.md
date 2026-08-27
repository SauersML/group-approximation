---
rg: 2
id: sofic-kernel-amenable-quotient-permanence
kind: claim
title: A group with sofic kernel and amenable quotient is sofic
artifacts:
  - GroupApproximation/Sofic/SoficByAmenablePermanence.lean
  - GroupApproximation/Sofic/SoficIntegerExtension.lean
  - non_mf_groups_exist.tex
---

Let `N` be a normal subgroup of `G`.  If `N` is sofic and `G/N` is amenable,
then `G` is sofic.  No splitting and no countability hypothesis is needed.

In particular, if `K` is sofic and `phi` is an automorphism of `K`, then

```text
K semidirectProduct_phi Z
```

is sofic.

This is the valid direction used by `literal-sofic-via-block-tower`.  It is
not the amenable-kernel/sofic-quotient implication attempted by the refuted
route `literal-sofic-via-amenable-kernel`.
