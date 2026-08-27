---
rg: 2
id: three-reynolds-plus-kernel-energy-has-vanishing-gap
kind: claim
title: Three regular Reynolds legs plus every commuting kernel-word energy have no uniform diagram gap
distinct_from:
  relative-finite-group-gh-cannot-fix-two-generating-subgroups: that gives the two-leg exact-support obstruction and the alternating-projection rate; this adds a third regular leg, an exactly regular eight-point character table, all three quotient kernel words, and computes the full positive diagram Laplacian.
  finite-group-intertwiner-laplacian-gap: that fixes the finite representations and obtains a gap off the exact intertwiner space; here the finite subgroup representations rotate by an amount tending to zero, making the angle between their exact intertwiner spaces collapse.
  km-kazhdan-holonomy-rounding-starts-after-projective-flatness: that applies a Kazhdan gap after every adjoint relator is exact; this shows that adding the squared adjoint relator errors to the local Reynolds Laplacians does not manufacture such exactness.
  native-km-coset-coefficients-retain-spherical-pauli-absorber: that writes the unreduced P12/P13/P23 coset-incidence maps, computes the B2 orthogonal coefficient gap, and embeds the Pauli rotation in their common spherical multiplicity block; this supplies the scalarized benchmark.
---

**ESTABLISHED.**  Let `A,B,C,F` be the three-qubit Pauli tensors

```text
A=Z tensor I tensor I,       B=I tensor Z tensor I,
C=X tensor Y tensor I,       F=I tensor I tensor Z,
D_t=cos(2t)B+sin(2t)C,             0<t<pi/4.          (DRK1)
```

The involutions `A,D_t,F` give a normal-form table for
`Q=(C_2)^3` by

```text
phi_t(e,f,g)=A^e D_t^f F^g.                            (DRK2)
```

It is exact on every cyclic factor and on the pairs `(A,F)` and `(D_t,F)`.
Its normalized trace is **exactly** the regular character of `Q`, and every
multiplication defect is at most

```text
delta_t=2sin(2t)->0.                                   (DRK3)
```

Write the three commuting quotient-kernel words as

```text
Y_12=AD_tAD_t,       Y_13=AFAF=I,       Y_23=D_tFD_tF=I. (DRK4)
```

On normalized Hilbert--Schmidt space put

```text
E_U(T)=(T+UTU)/2,
L_t=sum_(U in {A,D_t,F})(I-E_U)
    +sum_(ij in {12,13,23})(I-Ad(Y_ij))^*(I-Ad(Y_ij)). (DRK5)
```

This is the literal positive operator obtained by summing the three relative
conditional-expectation Laplacians and **all** quotient kernel-word adjoint
energies.  Nevertheless its spectral gap above its kernel satisfies

```text
gap(L_t)<=1-cos(2t)+4sin^2(4t)->0.                     (DRK6)
```

Indeed the right side is an actual eigenvalue on the trace-zero plane
`span_R{B,C}`.  Tensoring every matrix by `I_m` gives arbitrary dimension,
preserves the exactly regular character and every normalized defect, and
leaves `(DRK6)` unchanged.

Consequently no diagrammatic Poincare inequality follows merely from:

1. canonical regular finite-factor character tables;
2. the three exact subgroup Reynolds projections; and
3. the sum of squared adjoint energies of every quotient kernel word.

This is a direct falsification benchmark for the section-built approximate
`P_13` chart: two of the three legs can be perfectly flat and the remaining
kernel defect can tend to zero while the full proposed diagram angle still
collapses quadratically.  A surviving Kac--Moody inequality must use a
coefficient identity specific to its rank-two vertex character tables that
excludes the Pauli rotation.  Treating the native kernel words only through
their norms or adjoint Laplacians cannot provide the desired dimension-free
constant.

Passing back to the unreduced native coefficient maps does not remove the
counterpacket.  `native-km-coset-coefficients-retain-spherical-pauli-absorber`
computes their `B_2` incidence gap off constants, but shows that their common
constant coset line tensored with multiplicity is reducing.  A single native
free-kernel chord can carry `AD_tAD_t` in that block while every local
coefficient equation remains exact.
