---
rg: 2
id: kt-fell-haagerup-wall-free-proof
kind: route
title: Transfer walls to the coefficient, where the Haagerup no-wall theorem applies
target: kt-fell-models-over-haagerup-coefficients-are-wall-free
requires: [fell-models-inherit-walls-from-coefficients, kt-polynomial-subgroup-is-icc-in-kt-group, haagerup-targets-carry-no-relative-wall, kun-thom-nonsofic-wreath]
---

1. By `kt-polynomial-subgroup-is-icc-in-kt-group`, `Gamma` and all its
   `G`-conjugates have infinite conjugacy classes on `G - {e}`. So
   `fell-models-inherit-walls-from-coefficients` gives
   `(L(G) tensor-bar M_0) cap sigma(Gamma)' = 1 tensor (M_0 cap pi(Gamma)')`, with
   `Ad sigma(g)` acting as `1 tensor Ad pi(g)`.
2. `Gamma` has property (T) and is infranormal in `G` (Kun--Thom Theorem E,
   `kun-thom-nonsofic-wreath`), and `pi(Gamma)''` is Haagerup. So
   `haagerup-targets-carry-no-relative-wall` applied to `pi` shows that
   `M_0 cap pi(Gamma)'` is `Ad pi(G)`-invariant, and no family in it has stabilizer
   `Gamma`, since `Gamma` is not normal.
3. By step 1, both conclusions transfer verbatim to `sigma`.
