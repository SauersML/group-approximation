---
rg: 2
id: sln-z-unipotent-spectrum-finite-or-full-torus-proof
kind: route
title: Invariant closed subsets of the torus are finite or everything, and level-N elementary matrices normally generate the congruence kernel
target: sln-z-unipotent-spectrum-finite-or-full-torus
requires: [sln-z-principal-congruence-elementary-generated]
artifacts:
  - research/artifacts/sl4z-mf-corona-reduction-2026-09-13-part2.md
---

Artifact part 2, Section 1.

1. **Invariance.**  `diag(A,1) u(v) diag(A,1)^-1 = u(Av)`, and
   `exp(2 pi i theta . Av) = exp(2 pi i (A^T theta) . v)`.  So `Ad sigma(diag(A,1))` maps
   `sigma(f)` to `sigma(f o A^T)` on `C*(U) = C(T^(d-1))`.  Hence `Y` is closed and
   `SL_(d-1)(Z)`-invariant.
2. **Lemma 1: a closed invariant set is finite torsion or the whole torus.**  Let
   `m = d - 1 >= 2`.
   - *A point with irrational coordinate `theta_j`.*  `I + e_(ij)` sweeps out the circle
     `theta + T e_i`.  Fix coordinate `i` at an irrational value, then sweep every other
     coordinate with `I + e_(ki)`.  So `Y = T^m`.
   - *All points torsion, orders bounded.*  Then `Y` is finite.
   - *All points torsion, orders unbounded.*  Some coordinate `j` has order `N_s -> inf`
     along a sequence of points.  Its multiples fill `(1/N_s)Z/Z`, so `Y` contains
     `1/N_s`-dense subsets of circles `theta^(s) + T e_i`.  In the limit it contains a full
     circle, and the first case applies.
3. **Lemma 2: finite spectrum gives a congruence quotient.**
   - Finite `Y` with lcm of orders `N` gives `sigma(u(Nv)) = 1`.
   - Signed permutation matrices in `SL_d(Z)` (`d >= 3`) conjugate `I + N e_(1,d)` to
     `I +- N e_(k,l)` for all `k != l`.  So `ker sigma|_Gamma` contains the normal
     closure `E_d(Z, NZ)`.
   - By `sln-z-principal-congruence-elementary-generated`, that closure equals
     `ker(SL_d(Z) -> SL_d(Z/NZ))`.
