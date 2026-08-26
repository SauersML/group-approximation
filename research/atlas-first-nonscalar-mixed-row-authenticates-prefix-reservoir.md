---
rg: 2
id: atlas-first-nonscalar-mixed-row-authenticates-prefix-reservoir
kind: route
title: The first non-scalar mixed-direction Atlas row authenticates the prefix reservoir
target: paired-same-reservoir-boundary-lemma
requires: []
---

**REFUTED.** In the canonical order of the rank-five packet, after omitting
one-root rows, rows with two roots of the same orientation, and rows with a
constant coefficient on either side, the first remaining row is

```text
orth_12_32_ee = [x_12(e),x_32(e)].
```

It is a same-source Steinberg commutation identity. The two off-diagonal
blocks multiply to zero in both orders for arbitrary coefficient maps and
arbitrary source/target object dimensions. It therefore contributes no
coarse-to-fine multiplicity authentication, even when appended exactly to a
coherent prefix tower. See
`atlas-first-nonscalar-mixed-row-is-same-source-commutation`.
