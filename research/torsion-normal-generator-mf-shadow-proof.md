---
rg: 2
id: torsion-normal-generator-mf-shadow-proof
kind: route
title: Reblock every MF-visible torsion mark into an HS-visible operator model
target: torsion-normal-generator-mf-shadow-equivalence
requires:
  - torsion-normal-generator-has-full-support-corona-core
  - op-to-hs-shadow-residual-functoriality
---

The general inclusion

```text
Rad_MF(G)<=R_(infinity->2)(G)                          (MSE3)
```

follows by passing every operator-norm asymptotic representation to its norm
corona homomorphism: an MF-invisible element is norm-null and therefore
normalized-Hilbert--Schmidt-null.

For the converse at `a`, suppose `a` is not in `Rad_MF(G)`.  Some norm-corona
homomorphism sees `a`.  Apply torsion active-core reblocking.  It produces an
operator-norm asymptotic representation `sigma_n` and constants
`eta_m>0`, `L<infinity` such that

```text
liminf_n ||sigma_n(a)-1||_2>=eta_m/sqrt(L)>0.          (MSE4)
```

Thus `a` is not in `R_(infinity->2)(G)`.  Taking the contrapositive and
combining with `(MSE3)` proves `(MSE1)`.

If `G` is simple, each residual is either `1` or `G`.  Their membership
decision on the fixed nonidentity torsion element is the same by `(MSE1)`,
so the two normal subgroups are equal.

