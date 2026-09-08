---
rg: 2
id: del2-three-dimensional-head-braid-gap-proof
kind: route
title: Eliminate the two standard-coordinate braid blocks while retaining both head chiralities
target: del2-three-dimensional-head-braid-gap
requires:
  - binary-jacobson-gl3-k-branching-has-regular-counterprofile
artifacts:
  - research/artifacts/del2-three-dimensional-head-braid-gap.md
---

Use the two three-dimensional head types and their common
`K`-restriction `sign directSum standard` certified by the required node.
The elementary three-axis frame computation in the artifact puts the
positive line of `rho_+(b)` in a common real `K`-basis at

```text
v=(1/sqrt(6),1/2,i sqrt(7/12)).
```

The conjugate head type has the conjugate positive line. On
`W=W_+ directSum W_-`, encode its sign by
`J=I_(W_+) directSum -I_(W_-)`, and put
`M=sigma_+(b) directSum sigma_-(b)`. These two involutions commute.
Schur's lemma makes every allowed `H` equal to `diag(A,C,C)`, where
`A,C` can mix the two chirality spaces arbitrarily.

Let `delta=||(HB)^3-I||=||HBH-BHB||`, where `B=pi(b,b)`.
Write `d=MAM`, `e=MCM`, and let `R_22,R_33` be the two standard-coordinate
diagonal blocks of `HBH-BHB`. Direct multiplication gives

```text
R_22=-(1/2)CMC-(1/6)d-(1/4)e-(7/12)JeJ,
R_33= (1/6)CMC-(7/18)JdJ-(7/12)JeJ-(1/36)e.
```

Set `D=d+2e=M(A+2C)M`. Eliminating `CMC` yields

```text
D+7JDJ=-6R_22-18R_33,
6||D|| <= ||D+7JDJ|| <= 24 delta.
```

Since `||D||=||A+2C||>=1`, the primary bound is `delta>=1/4`.
For a single head type one can rotate the standard basis to put the
head involution into a real two-by-two block plus `-1`. The artifact
then eliminates two braid blocks to obtain the sharper `delta>=1/3`.
No estimate depends on the tail dimension or multiplicities.

A trivial-head summand is a sum of trivial `K`-types, absent from
`rho_+|_K` and `rho_-|_K`. Thus every overlap-central `H` preserves
the three-dimensional head part after such summands are added.
Restricting the braid defect to that nonzero invariant subspace proves
the stated extension.
