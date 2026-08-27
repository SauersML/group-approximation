---
rg: 2
id: sl3-one-parahoric-tracezero-gauge-proof
kind: route
title: Tensor one parahoric packet with a free cyclic multiplicity shift
target: sl3-one-parahoric-multiplicity-flow-has-a-tracezero-gauge
requires: []
artifacts:
  - research/artifacts/sl3-one-parahoric-multiplicity-flow-audit-2026-08-21.md
---

The spectator factor in `(PMG6)` is trivial for `C`.  Hence `I tensor V`
commutes with every source matrix and inserting it in the second transport
does not change either parahoric conjugacy equation.  Restriction and
induction multiplicities are multiplied by the same `m`, so normalized flow
is unchanged.

Formula `(PMG7)` follows from multiplicativity of normalized trace under
tensor products, and a cyclic shift has trace zero.  Finally
`[I tensor V,pi(c) tensor I]=0` for every `c`, proving that all source and
coset-expander energies vanish on this non-scalar gauge.
