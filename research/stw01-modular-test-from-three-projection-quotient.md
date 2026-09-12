---
rg: 2
id: stw01-modular-test-from-three-projection-quotient
kind: route
title: The modular-group algebra is a quotient of the three-projection algebra
target: stw01-modular-group-algebra-quasitraces-are-traces
requires:
  - stw01-three-projection-algebra-quasitraces-are-traces
---

There are unital surjections

```text
P_3 = C^2 * C^2 * C^2  ->  C^4 * C^2  ->  C^3 * C^2 = C*(PSL_2(Z)).
```

- The first abelianizes the pair `r_1, r_2`. The abelianization of the
  two-projection algebra is `C^4`, spanned by `r_1 r_2`, `r_1(1 - r_2)`,
  `(1 - r_1) r_2` and `(1 - r_1)(1 - r_2)`. The map keeps `r_3`.
- The second merges two of the four minimal projections of `C^4`.
- A unital full free product of unital surjections is a unital surjection.

Bounded 2-quasitraces pull back along unital surjections, and a non-linear one stays
non-linear. So if every bounded 2-quasitrace on `P_3` is a trace, the same holds on
`C^3 * C^2`.

The reverse implication goes through Problem I:
`stw01-problem-i-via-modular-group-algebra`. Details are in
`research/artifacts/stw01-modular-group-universal-test-2026-09-12.md`.
