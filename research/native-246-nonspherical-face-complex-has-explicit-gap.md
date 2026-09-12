---
rg: 2
id: native-246-nonspherical-face-complex-has-explicit-gap
kind: claim
title: The native (2,4,6) nonspherical face complex has gap 1-sqrt(3q)/(q+1)
distinct_from:
  native-km-coset-coefficients-retain-spherical-pauli-absorber: that computes only the B2 coefficient and finds the spherical overlap-coordinate zero mode; this computes all A1xA1, B2, and G2 spectra and quotients that gauge mode.
  full-km-face-kills-no-spherical-gauge: that proves the spherical mode is freely correctable; this proves a uniform lower bound on its orthogonal finite-label complement.
  relative-three-chart-correction-is-km-regular-stability: that is the nonlinear exact-chart synchronization target; this is the complete fixed linear occurrence-complex estimate, conditional only on placing the three chart errors in one common occurrence decomposition.
---

**ESTABLISHED.**  For each native rank-two parabolic `P_ij`, let `N_ij`
be the point-line incidence matrix of

```text
P_ij/P_i  <-  P_ij/P_0  ->  P_ij/P_j,                 (NFC1)
```

and normalize it by `T_ij=N_ij/(q+1)`.  For the explicit Coxeter types
`(m_12,m_13,m_23)=(2,4,6)`, the singular spectra are

```text
sing(T_12)={1,0},
sing(T_13)={1,sqrt(2q)/(q+1),0},
sing(T_23)={1,sqrt(3q)/(q+1),sqrt(q)/(q+1),0}.          (NFC2)
```

The singular value `1` is simple and belongs to the constant spherical
vectors.  Therefore, if `Q_(ij,i),Q_(ij,j)` are the two orthogonal range
projections in the chamber occurrence space and

```text
Delta_ij=(I-Q_(ij,i))+(I-Q_(ij,j)),                    (NFC3)
```

then, after quotienting their common spherical range,

```text
Delta_12 >=1,
Delta_13 >=1-sqrt(2q)/(q+1),
Delta_23 >=1-sqrt(3q)/(q+1).                           (NFC4)
```

All estimates persist after tensoring the occurrence spaces with arbitrary
matrix multiplicity algebras.  Consequently the block face operator

```text
Delta_face=Delta_12 direct-sum Delta_13 direct-sum Delta_23              (NFC5)
```

has, modulo the direct sum of its spherical gauge blocks, the uniform gap

```text
kappa_246(q)=1-sqrt(3q)/(q+1)>0.                       (NFC6)
```

The shared-rank-one compatibility maps are equally concrete.  Put all three
regular charts in a common dimension `D`.  The `P_i`-fiber-constant range in
either adjacent chart has dimension

```text
[P_ij:P_i]D/|P_ij|=D/|P_i|.                            (NFC7)
```

Choose fixed occurrence unitaries `U_(ij,i)` from those two equal-dimensional
ranges to one space `K_i`.  For `{j,k}={1,2,3}\{i}`, set

```text
B_i(x)=U_(ij,i)Q_(ij,i)x_ij-U_(ik,i)Q_(ik,i)x_ik,
C=sum_(i=1)^3 B_i^*B_i.                                (NFC8)
```

This is the unreduced linear compatibility operator identifying the two
occurrences of each `P_i`; different choices of the `U_(ij,i)` conjugate it
by block gauges.  More generally one may add any further positive
compatibility squares.  If the kernel of `Delta_face+C` is exactly the
spherical gauge already removed, then

```text
Delta_face+C >=kappa_246(q) I                          (NFC9)
```

on the quotient.  Thus no genuine nonspherical Pauli absorber exists in a
common linear occurrence model: its component in every face pays at least
`kappa_246(q)` times its squared normalized-HS norm.  Its spherical component
is the zero-cost gauge treated by `full-km-face-kills-no-spherical-gauge`.

This closes the **finite linear coefficient** calculation with an exact
constant.  It does not by itself construct the required common occurrence
model from independently Gowers--Hatami-exactified charts.  A nonlinear
counterpacket, if one exists, must prevent those three exactifications from
being placed in this fixed decomposition while remaining close in normalized
HS norm; it cannot live in the native A1xA1, B2, or G2 character-table
matrix once that placement is available.
