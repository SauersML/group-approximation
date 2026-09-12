---
rg: 2
id: leavitt-unit-internal-shift-reflection
kind: claim
title: The binary Leavitt MF black hole contains its own bilateral wreath shift
root: true
artifacts:
  - research/leavitt-unit-internal-shift-proof.md
---

Let

```text
U=L_(F_2)(1,2)^x.
```

There is an explicit embedding

```text
W_Z=U^(Z) semidirectProduct Z = U wr Z  <= U,            (IS1)
```

where `Z` shifts the coordinates.  The subgroup `W_Z` is finitely generated,
and

```text
Rad_MF(W_Z)=U^(Z),       W_Z/Rad_MF(W_Z) ~= Z.           (IS2)
```

Every homomorphism from `W_Z` to an MF group factors uniquely through the
height map `W_Z->Z`.  The same factorization holds for finite groups,
residually finite groups, compact Hausdorff groups, and finite-dimensional
linear groups over every field.  Thus `W_Z` has the same complete MF-target,
profinite, Bohr, and exact finite-dimensional representation functors as
`Z`, despite being non-MF.

The radical is the normal closure of one nonidentity involution `d` in the
zeroth coordinate.  For every normal subgroup `N` of `W_Z`,

```text
cl_MF^(W_Z)(N)=N normalClosure_(W_Z)(d),                 (IS3)
W_Z/N is MF  iff  d belongs to N.                        (IS4)
```

Consequently one fixed simple finitely generated Kazhdan MF black hole
contains a finitely generated subgroup with infinite cyclic universal MF
quotient and a one-relation MF phase transition across its entire quotient
lattice.
