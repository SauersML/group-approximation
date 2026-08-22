---
rg: 2
id: finite-spherical-quadrature-proof
kind: route
title: Apply joint spectral calculus and Caratheodory to the quasi-regular Hecke state
target: finite-spherical-moments-do-not-fold-regular-double
requires:
  - sl3-double-tensor-leak-is-quasiregular
  - hecke-averaging-realizes-commutant-expectation
  - sl3-arithmetic-double-finite-representations-fold
---

The first required claim identifies the regular-double block-swap cyclic
state with the quasi-regular coefficient `1_C`.  The spherical Hecke algebra
of `(SL_3(Q_2),SL_3(Z_2))` is commutative, so joint spectral calculus gives
its compact spectral measure.  Caratheodory plus rational approximation
proves `(FSM1)` and realizes the quadrature by finite diagonal matrices.

The second required claim supplies the explicit lazy Hecke polynomial and
its quasi-regular value.  The third explains why these abstract atoms cannot
be promoted to exact finite-dimensional group models: extension would turn
the `C`-fixed carrier into an `A`-fixed carrier and fold the two vertices.
Hence group-extension compatibility, absent from quadrature, is exactly the
remaining datum.
