---
rg: 2
id: non-hyperlinear-from-p3-relative-commutant-collapse
kind: route
title: The p three pair reaches the goal through relative-commutant collapse
target: non-hyperlinear-group
requires:
  - hnn-route-is-relative-commutant-collapse
  - sl3-p3-pair-relative-commutant-collapse
---

Instantiate the established reduction at `A = SL_3(Z[1/3])`,
`C = SL_3(Z)`, `a_1 = h = diag(3, 1, 1/3)`: the pair is proper and
co-dense, so the finitely presented group

```text
G_3' = < SL_3(Z[1/3]), t | [t, SL_3(Z)] = 1 >
```

is not hyperlinear as soon as `(RC3-p3)` holds — the statement of
`sl3-p3-pair-relative-commutant-collapse`. This is a sharp goal edge,
but its open input is the full RCC statement. The proposed closure of
the `Lambda`-exact face is not established: nonuniform Folner profiles
and the parahoric-to-Weil transport dictionary remain open in addition
to the uniform-outlier sector.
