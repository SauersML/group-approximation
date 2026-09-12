---
rg: 2
id: master-host-determinant-via-euler-integrality
kind: route
title: Prove the determinant conjecture for every torsion-free group from integrality of trace zeta series
target: master-host-satisfies-determinant-conjecture
requires:
  - torsion-free-integral-zeta-is-an-integer-euler-product
  - euler-integral-measures-are-serre-class
  - determinant-conjecture-iff-serre-class-spectra
---

The master tester `E` is torsion-free. Let `T in M_n(Z[E])` be self-adjoint.

- For every `Q in Z[x]`, the matrix `Q(T)` is self-adjoint and integral, so its
  trace zeta series is an integer Euler product
  (`torsion-free-integral-zeta-is-an-integer-euler-product`). Its moments are
  `integral Q^j d mu_T`.
- So `mu_T` satisfies the hypothesis of `euler-integral-measures-are-serre-class`,
  and every Serre inequality holds for `mu_T`.
- By `determinant-conjecture-iff-serre-class-spectra`, `E` satisfies Lück's
  determinant conjecture.

The same argument covers every torsion-free group directly. No approximation of
the group is used anywhere; soficity is replaced by an arithmetic statement
about measures.
