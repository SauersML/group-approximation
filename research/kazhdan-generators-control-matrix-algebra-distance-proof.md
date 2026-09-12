---
rg: 2
id: kazhdan-generators-control-matrix-algebra-distance-proof
kind: route
title: Haar-average the Kazhdan commutator inequality over the target algebra commutant
target: kazhdan-generators-control-matrix-algebra-distance
requires: []
artifacts:
  - research/artifacts/kazhdan-carrier-uniformization-2026-09-08.md
---

Write `R=A' cap M_d`. The conjugation representation of `C` on the
normalized Hilbert--Schmidt space is exact, with fixed subspace `R`.
Its Kazhdan inequality gives, for every `v in U(B' cap M_d)`,

    ||v-E_R(v)||_2^2
      <= kappa^(-2)sum_(s in S)||[v,sigma(s)]||_2^2.

Since `x in A` commutes with `E_R(v)`,

    ||[v,x]||_2^2
      <=4||x||_op^2||v-E_R(v)||_2^2.

The normalized Haar average of `y -> v y v*` over `U(B' cap M_d)`
is `E_B`: its fixed algebra is the matrix bicommutant `B`. Therefore

    integral ||[v,y]||_2^2 dv = 2||y-E_B(y)||_2^2

for every matrix `y`. Integrate the preceding inequalities and cancel
the factor two to obtain `(KCU1)`. This applies to the entire unit ball
of `A` at once, even when `A` and `x` change with the matrix coordinate.
