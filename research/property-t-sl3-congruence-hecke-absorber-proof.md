---
rg: 2
id: property-t-sl3-congruence-hecke-absorber-proof
kind: route
title: Realize the finite Hecke packet in the octahedral subgroup and odd congruence quotients
target: property-t-does-not-repair-the-finite-hecke-router
requires:
  - single-hecke-transport-cannot-carry-complete-context
---

# Proof

Let
```text
O_3(Z)^+={signed permutation matrices of determinant one}.
```
This is the rotational octahedral group, of order 24, hence isomorphic to
S_4, and it is a subgroup of SL_3(Z).  Choose an isomorphism carrying the
abstract elements
```text
r=(1 2 3 4),  s=(1 3),  t=(3 4)
```
to this subgroup.  Inside it set
```text
E=<r,s> isomorphic to D_8,
J=r^2,                 a=rs.
```
The identities
```text
t a t^-1=J,            t J t^-1=a                         (PTH1)
```
hold in SL_3(Z).

In the group algebra define
```text
q=(1-J)/2,
p_+=q(1+a)/2,          p_-=q(1-a)/2.
```
They obey, algebraically,
```text
q t p_+ t^-1 q=0,
q t p_- t^-1 q=p_-,
q t q t^-1 q=p_-.                                      (PTH2)
```
These equations use only (PTH1), so they hold in every representation.

For every odd prime ell, reduction modulo ell is injective on the signed
permutation subgroup: two distinct signed monomial matrices still differ
modulo ell.  Hence the congruence quotient
```text
SL_3(Z) -> SL_3(F_ell)
```
contains the same copy of S_4.  Let lambda_ell be the left regular
representation of the finite quotient.  Its normalized character is
zero on every nonidentity element, so on the S_4 subgroup it is a
multiple of the regular character.  Therefore
```text
tau_ell(q)=1/2,
tau_ell(p_+)=tau_ell(p_-)=1/4,                            (PTH3)

||(1-q)lambda_ell(t)^*q||_2^2=1/4,
||q-lambda_ell(t)q lambda_ell(t)^*||_2^2=1/2.             (PTH4)
```
In (PTH4), the second expression denotes the distance between q and
`lambda_ell(t)q lambda_ell(t)^*); the first equality is the
off-corner leakage formula.  More explicitly,
```text
||q-lambda_ell(t)q lambda_ell(t)^*||_2^2
 =2[tau_ell(q)-tau_ell(qtqt^-1)]=1/2.
```

The left regular representation of SL_3(Z) has the identical values,
because its canonical trace also restricts to the regular trace on every
finite subgroup.  Thus the infinite regular model and every odd
congruence regular model agree exactly on the complete Hecke packet.

Finally, SL_3(Z) has Kazhdan property (T).  Equations (PTH3)--(PTH4) show
that property (T) alone cannot make this particular corner approximately
invariant under t: exact property-(T) representations already have fixed
off-corner mass.  A Kazhdan estimate can apply only after additional
relations make the corner vector or projection nearly invariant under a
Kazhdan set.  If they make q invariant under t itself, the compression is
reducing and returns to the normalizer regime.

The same argument works in any residually finite host in which the finite
Hecke packet survives in finite quotients.  Property (T) and residual
finiteness are therefore compatible with exact finite absorbers; neither
one supplies the missing nonreducing leakage decoder.
