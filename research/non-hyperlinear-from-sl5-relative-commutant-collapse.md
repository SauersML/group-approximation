---
rg: 2
id: non-hyperlinear-from-sl5-relative-commutant-collapse
kind: route
title: The rank-four pair reaches the goal through the established reduction once its collapse holds
target: non-hyperlinear-group
requires:
  - hnn-route-is-relative-commutant-collapse
  - sl5-pair-relative-commutant-collapse
---

Instantiate the established reduction
`hnn-route-is-relative-commutant-collapse` at `A = SL_5(Z[1/2])`,
`C = SL_5(Z)`, `a_1 = h = diag(2, 1, 1, 1, 1/2)`:
the pair is proper and co-dense
(`sl5-pair-relative-commutant-collapse`), so

```text
G_5 = < SL_5(Z[1/2]), t | [t, SL_5(Z)] = 1 >
```

is a finitely presented group that is not hyperlinear as soon as
`(RC5)` holds for every regular-trace representation into a tracial
matrix ultraproduct -- which is the statement of
`sl5-pair-relative-commutant-collapse`.

This is the third goal edge of the relative-commutant lane (after
`n = 2` and `n = 3`), added because the degree-2 cohomology
infrastructure (Bader--Sauer `(T_2)`, `(T_3)`) exists only for
`N >= 4`: if a normalized-HS stability criterion materializes there,
the goal follows on this edge with no further graph work.
