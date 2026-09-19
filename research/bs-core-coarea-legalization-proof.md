---
rg: 2
id: bs-core-coarea-legalization-proof
kind: route
title: Cut a long fourth-power orbit into a half interval
target: bs-core-coarea-cuts-have-full-legalization-cost
requires:
  - bs14-unitary-representations-are-periodic-cycle-packets
---

The relation `R_m S_m R_m^*=S_m^4` is immediate.  The order of `4` modulo
`4^m-1` is exactly `m`, so the eigenvalues of `S_m` are distinct.  An
operator commuting with `S_m` is diagonal; commuting also with the cyclic
shift makes that diagonal constant.  The joint commutant is therefore the
scalar line.

Translation by `R_m` changes the half interval at exactly two endpoints,
so `||[P_m,R_m]||_F^2=2`.  The distances squared from `P_m` to `0` and `1`
are its rank and corank, proving `(BCC3)`.

