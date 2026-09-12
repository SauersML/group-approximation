---
rg: 2
id: odd-selector-overlap-rounding-proof
kind: route
title: Joint-spectrum counting proves one-hot selector rounding
target: odd-selector-overlap-rounding
requires: []
artifacts:
  - research/artifacts/selector-overlap-rounding-2026-08-18.md
---

Use the joint spectral decomposition of the commuting projections `P_a`.  On a
joint atom let `h` be the number of hot selectors.  Then `Q=1` exactly when
`h=1`,

```text
sum_(a<b) P_a P_b = binom(h,2),
W=(-1)^h,
(1/4)|W+1|^2 = 1_(h even).
```

Pointwise,

```text
1_(h!=1) <= 1_(h even) + binom(h,2),
```

which integrates to the first bound.  If `W=-1`, only odd `h` occur; every
bad atom has `h>=3`, hence `binom(h,2)>=3`, giving the `S/3` improvement.

Finally `Q_a<=P_a`, so

```text
||P_a-Q_a||_2^2=tau(P_a-Q_a).
```

The sum of these quantities contributes `h` on an atom with `h!=1` and zero
when `h=1`.  For every `h>=2`, `h<=2 binom(h,2)`, while at `h=0` both sides
are zero.  Integrating proves the second bound.
