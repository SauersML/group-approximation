---
rg: 2
id: sl3z-contains-f2-times-f2
kind: claim
title: SL_3(Z) contains a subgroup isomorphic to F_2 x F_2
refuted_by: sl3z-products-of-infinite-subgroups-are-polycyclic
---

`SL_3(Z)` contains a subgroup isomorphic to `F_2 x F_2`. This is the source of
incoherence for `SL_n(Z)` with `n >= 4`, where `SL_2(Z) x SL_2(Z)` sits in
block form.

Refuted: two commuting infinite subgroups of `SL_3(Z)` generate a polycyclic
group (`sl3z-products-of-infinite-subgroups-are-polycyclic`), and `F_2 x F_2`
is not polycyclic.

## Attempts

- Refuted 2026-09-13 (z3-04-sl3z-incoherent); see `refuted_by`. The route
  `sl3z-incoherent-via-f2-times-f2` is therefore dead.
