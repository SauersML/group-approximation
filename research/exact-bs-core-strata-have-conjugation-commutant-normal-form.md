---
rg: 2
id: exact-bs-core-strata-have-conjugation-commutant-normal-form
kind: claim
title: Each exact BS-core torsion stratum is a conjugation orbit followed by one root-commutant fiber
distinct_from:
  optimized-core-one-sided-normal-slice-is-exactly-coercive: that proves the quantitative row identity on one fixed-root fiber; this proves that those fibers, together with common conjugation, exhaust every exact core in a fixed root-multiplicity stratum.
  iwahori-torsion-multiplicity-stratum-reconciliation: that asks to pass uniformly between different nearby strata with flexible rank; this gives an exact global chart only after the root multiplicity vector is fixed.
  congruence-iwahori-endpoint-fiber-contains-core-commutant-orbits: that classifies extending Weyl matrices over one fixed regular core; this classifies the BS cores themselves before an extending Weyl matrix is selected.
---

Let

```text
b_i=(R_i,T_i),              i=0,1,                    (BCS1)
```

be exact level-`N` BS cores, and assume that `T_0` and `T_1` have the same
multiplicity at every `N`th root of unity.  Then there are unitaries `z,q`
such that

```text
T_1=zT_0z^(-1),
R_1=q zR_0z^(-1),
q in {T_1}'.                                          (BCS2)
```

Conversely, every pair `(z,q)` satisfying `(BCS2)` produces another exact
level-`N` BS core from `b_0`.  Thus a fixed torsion-multiplicity stratum of
the exact-core variety is globally exhausted by common conjugation and the
one-sided root-commutant fibers.

There is a quantitative endpoint consequence.  If `(X_0,R_0,T_0)` is an
exact endpoint and `X_1=zX_0z^(-1)`, then

```text
G_N(X_1,b_1) <= 2 E_end(X_1,b_1).                     (BCS3)
```

Hence operator-large or small-rank motion anywhere inside a fixed exact
core stratum is harmless whenever the extending involution follows the
conjugation coordinate.  After quotienting that symmetry, the surviving
nonlinear variables are precisely endpoint-orbit mismatch and changes of
the root torsion-multiplicity vector.

