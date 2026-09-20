---
rg: 2
id: hyperlinear-rf-gluing-failure-by-kt-examples
kind: route
title: Inspect the kernel quotient vertices and edge of the nonhyperlinear Kun--Thom examples
target: hyperlinear-rf-gluing-permanence-fails
requires:
  - kun-thom-nonsofic-wreath
  - kun-thom-lamp-wreath-is-not-hyperlinear
  - kt-q2-double-is-not-hyperlinear
---

The structural first premise supplies residually finite Gamma and G for
q=2,r=d=3 and for q=2,r=6,d=3. In the wreath, the lamp kernel
direct_sum_(G/Gamma) C_2 is abelian and locally finite. Coordinate
projections distinguish each nonzero configuration in a finite group,
so it is residually finite too; the extension splits with quotient G.
The second premise excludes hyperlinearity of this semidirect product.

The third premise excludes hyperlinearity of G_6 *_(Gamma_6) G_6;
its two vertices and its embedded edge are residually finite by the
first premise. Every countable residually finite group is hyperlinear:
choose separating finite quotients and their regular permutation
representations, regarded as unitaries. This verifies the positive
properties of all constituent groups without assuming a closure theorem.

Jihao Liu's internality input and Andreas Thom's conditional normalization
and double argument are inherited from the two negative premises.
