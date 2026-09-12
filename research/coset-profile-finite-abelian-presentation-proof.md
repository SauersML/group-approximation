---
rg: 2
id: coset-profile-finite-abelian-presentation-proof
kind: route
title: Present a coset profile by the annihilator equations of a finite phase group
target: finite-phase-scalar-groupification-iff-coset-subgroup
requires:
  - fixed-central-phase-scalar-profiles-form-coset-subgroup
---

Necessity is the required claim.  It remains to prove sufficiency.

Identify `mu_m^n` with the additive group

```text
A=(Z/mZ)^n
```

by `x |-> (zeta^(x_1),...,zeta^(x_n))`.  Let the prescribed nonempty set be
the coset `a+H`, where `H<=A`.  Under the perfect pairing

```text
<r,x> = sum_i r_i x_i  in Z/mZ,
```

put

```text
H^perp={r in A : <r,h>=0 for every h in H}.
```

Define the finite abelian group

```text
Gamma = < J,z_1,...,z_n |
          J^m=z_1^m=...=z_n^m=1,
          [J,z_i]=[z_i,z_j]=1,
          product_i z_i^(r_i)=J^(<r,a>)  (r in H^perp) >.       (C1)
```

The presentation is finite because `H^perp` is finite.  In a representation
with `J=zeta I` and scalar profile `z_i=zeta^(x_i)I`, the relations indexed by
`r` say exactly

```text
<r,x-a>=0 for every r in H^perp.                              (C2)
```

Finite Pontryagin duality for `A` gives

```text
(H^perp)^perp=H.                                               (C3)
```

Indeed the pairing identifies `A` with its character group.  The annihilator
of `H` therefore has order `|A|/|H|`; applying the same count to `H^perp`
gives (C3).  Thus (C2) holds exactly when `x in a+H`.

Conversely, for every `x in a+H`, the assignments

```text
J |-> zeta,                   z_i |-> zeta^(x_i)
```

satisfy (C1) and define a one-dimensional representation of `Gamma`.
Therefore the scalar profile set is precisely `a+H`.

If the prescribed profile set is empty, impose `J=1`; no representation can
then have `J=zeta I` because `zeta!=1`.

