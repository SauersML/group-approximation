---
rg: 2
id: paired-frame-forbidden-scalar-overlap-gap-proof
kind: route
title: Read the paired-frame self-hash from the optimal Reynolds transportation overlap
target: paired-frame-forbidden-scalar-overlap-gap
requires:
  - support-packet-covariant-wedderburn-detector
---

On every allowed sector the two commutant algebras have the same concrete
Wedderburn signature by `(CWD5)`.  Hence a unitary `W_k` conjugates one
commutant onto the other and therefore conjugates their Reynolds projections.
Substitution in `(PFO1)` gives `(PFO2)`.

On the forbidden sector the underlying Hilbert space has dimension `28m`,
while both Reynolds projections have rank `25m^2`, proving `(PFO3)`.  The
transportation-polytope calculation `(CWD7)` in the detector proof gives,
before normalization,

```text
Tr_super(R_+ Ad_W R_- Ad_W^*)<=17m^2                 (1)
```

for every unitary `W`.  Cyclicity and `R_+^2=R_+` identify the left side of
`(1)` with the unnormalized version of `(PFO1)`.  Division by
`(28m)^2=784m^2` proves `(PFO4)`.  Finally

```text
25/784-17/784=8/784=1/98,
```

which proves `(PFO5)`.  The equality alignment in the transportation proof
shows that `17/784` is sharp, although sharpness is not needed for the gap.
