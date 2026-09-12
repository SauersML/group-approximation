---
rg: 2
id: mdc-via-unimodular-network-serre
kind: route
title: Spread an integral groupoid-ring matrix over orbits as a unimodular integral network and apply the network Serre inequality to A*A
target: measure-theoretic-determinant-conjecture
requires:
  - serre-class-from-unimodular-integral-realizability
artifacts:
  - research/artifacts/unimodular-networks-mdc-2026-09-12.md
---

Artifact Section 1.2. Let `R` on `(X, mu)` be a measured equivalence relation
and `A in M_(m x n)(ZR)`.

1. **Reduction.** `B = A^* A in M_n(ZR)` is self-adjoint and
   `det A = det(B)^(1/2)`.
2. **Network.** On `[x] x {1..n}` put weights `w((y,i),(z,j)) = B_ij(y,z)`.
   These are symmetric integers with bounded weighted degree. Root at `(x,i)`
   with `x ~ mu` and `i` uniform, and keep the component of the root.
3. **Unimodularity.** Mass transport for the network is invariance of `mu`
   under `R`, applied to `F(x,y) = sum_(i,j) f(N_x, (x,i), (y,j))`. This works
   because the orbit networks satisfy `N_x = N_y` for `x ~ y`.
4. **Measure.** The expected root measure is the spectral measure of `B` for
   the normalized trace `(1/n) tr_n`.
5. **Conclusion.** The network Serre inequality with `Q = x` reads
   `log det B >= 0`, so `det A >= 1`.

**The cycle is intended.** Together with `unimodular-network-serre-via-mdc`
this route forms a two-claim cycle, because the claims are equivalent. A least
fixpoint establishes neither claim from the cycle alone. Do not delete either
route to silence the cycle warning.
