---
rg: 2
id: stw81-oinfinity-envelopes-have-dimension-one-or-infinity
kind: claim
title: O-infinity envelopes have empty hereditary shadows and dimension one or infinity
distinct_from:
  stw81-shadow-hypothesis-does-not-bound-primitive-spectrum: that treats the commutative-base examples C_0(X) tensor O_2; this allows an arbitrary nonzero separable, possibly noncommutative and nonnuclear, coefficient algebra and computes its envelope exactly.
  stw81-one-dim-elementary-oinfty-fields-have-dim-one: that globalizes fibrewise O-infinity absorption over a one-dimensional base; this starts with global O-infinity absorption and has no field or base-dimension hypothesis.
artifacts:
  - research/artifacts/stw81-oinfinity-envelope-audit-2026-08-30.md
---

Let `A` be any nonzero separable C-star algebra and put

```text
E=A tensor O_infinity.
```

No quotient of `E` contains a nonzero commutative hereditary C-star
subalgebra.  In particular, `E` satisfies the hereditary-shadow hypothesis
of Problem LXXXI in its strongest possible form.

Moreover, its nuclear dimension is computed exactly by

```text
dim_nuc(E) = 1          if A is nuclear,
dim_nuc(E) = infinity   if A is not nuclear.
```

Thus Problem LXXXI has a positive answer for every O-infinity envelope,
without any restriction on its primitive ideal space, ideal lattice, or the
topological dimension of a base space.
