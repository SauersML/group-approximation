---
rg: 2
id: stw95-nonunital-ash-factor-preserves-purity
kind: claim
title: Nonunital ASH factors preserve purity under the Seth--Vilalta hypotheses
distinct_from:
  stw95-transfinite-ash-layered-factor-preserves-purity: that theorem assembles ASH successor cells through an ordinal filtration; this is the local unitization-and-ideal theorem that removes unitality from each cell.
  stw95-one-zstable-factor-forces-pure-product: that theorem assumes Z-absorption and allows an arbitrary other factor; this theorem allows non-Z-stable pure inputs but requires the Seth--Vilalta simplicity or quotient-stable-finiteness hypothesis and an ASH factor.
  stw95-af-factor-external-cu-map-isomorphism: that theorem allows an arbitrary other factor and identifies the external Cu map, but only for AF factors; this theorem covers every separable ASH factor and concludes purity without identifying the external Cu map.
artifacts:
  - research/artifacts/stw95-nonunital-ash-unitization-audit-2026-08-30.md
---

Let `A` be a pure C-star algebra and assume either that

1. `A` is simple; or
2. every quotient of `A` is stably finite.

If `L` is a separable ASH C-star algebra, not necessarily unital, then

```text
A tensor_min L
```

is pure.

More generally, if `L` is a closed ideal in a unital separable ASH algebra
`D`, then `A tensor_min L` is pure.  No exactness or separability assumption
is imposed on `A`.

