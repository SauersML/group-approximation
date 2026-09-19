---
rg: 2
id: titz-witzel-sandwich-matchings-need-macroscopic-noncommutation
kind: claim
title: The two conjugate matchings in the Titz sandwich must macroscopically fail to commute
distinct_from:
  titz-witzel-two-generator-gate-forces-macroscopic-noncommutation: That forces the original matching `e` to fail to commute with the marked generator `u`, using only the first derived square; this forces two derived conjugates of `e` to fail to commute, using the final involution-sandwich equation.
  titz-witzel-both-matchings-need-macroscopic-support: That forces the old independent matchings `c,e` to move positive mass; this forces positive commutator mass between the derived matchings `beta,a`, which is strictly stronger than support alone.
artifacts:
  - research/artifacts/titz-witzel-involution-sandwich-check.py
---

**THEOREM.**  Use the involution-sandwich words from `(TWIS1)--(TWIS3)` in
`titz-witzel-two-generator-involution-sandwich-normal-form`.  In any group
with a bi-invariant metric, assume `e^2=1` and put

```text
delta_c = d(c^2,1),        eta_J = d(p u p c,1),
theta   = d(p^2,1)=d([beta,a],1).                         (TWSN1)
```

Then

```text
d(u^2,1) <= delta_c+2 eta_J+2 theta,                      (TWSN2)
d(u^8,1) <= 4 delta_c+8 eta_J+8 theta.                    (TWSN3)
```

Consequently, if finite-permutation models for the final gate have
`delta_c,eta_J -> 0` and

```text
limsup d_H(u^8,1)=epsilon>0,
```

then

```text
limsup d_H([beta,a],1) >= epsilon/8.                      (TWSN4)
limsup d_H(beta,a)      >= epsilon/16.                    (TWSN5)
```

Both `beta` and `a` are exact conjugates of the same matching `e`.  Thus a
positive solution requires not merely macroscopic support, but two
macroscopically different and macroscopically noncommuting placements of
that matching.  Equivalently, the alternating graph formed by the two
involutions has positive mass on components where the alternating product
has order greater than two.  This is a new necessary condition on a
construction; it does not decide the gate.

---

### Proof

titz-witzel-sandwich-noncommutation-proof
