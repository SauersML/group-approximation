---
rg: 2
id: period-doubling-walls-obstruct-finite-ground-energy
kind: route
title: Compute a reversible finite-seed orbit with unbounded walls at every period
target: reversible-ca-forbids-finite-ground-energy-compilers
requires: []
artifacts:
  - research/artifacts/finite-ground-energy-and-compiler-obstruction-2026-09-08.md
---

Represent a finite binary track by sum_i x_i z^(-i), so the shift
x_i->x_(i+1) is multiplication by z. The rule T has matrix
[[0,1],[1,1+z]]. With F_0=0, F_1=1, and F_(m+1)=u F_m+F_(m-1),
the isolated-b orbit has second coordinate F_(n+1)(1+z).

Squaring the matrix in characteristic two gives the doubling
identities. For N=2^k they imply

    F_(N-1)(1+z)=sum_(j=1)^k (1+z)^(N-2^j).

For 0<r<N the coefficient of z^r is v_2(r) modulo two. If
p=2^a q with q odd, positions r congruent to 2^(a+1) modulo
2^(a+2), with r+p<N, have opposite coefficients at r and r+p.
Their number tends to infinity as k grows.

A finite zero-energy subshift has a common positive spatial period
p. The compact cylinder of configurations differing at 0 and -p
is disjoint from it, so finitely many charged pattern tests cover
that cylinder. Translation bounds the total number of p-walls by
constant times total energy. The explicit orbit contradicts energy
nonincrease. The artifact proves all identities and the simulation
corollary by pulling back the target density along the local encoding.
