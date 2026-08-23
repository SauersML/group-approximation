---
rg: 2
id: separated-channel-identities-retain-rectangular-escape
kind: claim
title: Separated finite-carrier and Leavitt-coefficient identities retain the rectangular escape
distinct_from:
  rectangular-escape: that constructs the coefficient-side enlargement; this proves that tensoring it with any exact S3/S4 carrier leaves every separated carrier identity intact.
  s3-hard-cell-three-channel-data-is-nondegenerate: that proves the carrier matrices are invertible; this shows why those scalar determinants cannot by themselves invert external multiplicity operators.
  atlas-hard-packet-s3-channel-decoder: that asks for a mixed quotient-relator system in the same operator unknowns and is not ruled out by this no-go.
artifacts:
  - notes/FALSE_EQUIVARIANT_WHOLE_MAPS_ALLOW_RECTANGULAR_ESCAPE.md
---

Fix any finite carrier representation `C` satisfying prescribed exact
`S3/S4` branching, Clebsch--Gordan, recoupling, and finite determinant
identities.  Independently, for a perfect pairing `b:V x W -> F2`, put

```text
V'=V+V,  W'=W+W,
R0(v)=(v,0), R1(v)=(0,v),
L0(w)=(w,0), L1(w)=(0,w).                            (SCC1)
```

For the orthogonal-sum pairing `b'`,

```text
b'(Ri v,Lj w)=delta_ij b(v,w),                       (SCC2)
```

and all four maps are exactly translation-equivariant.  Tensor every
carrier operator with the identity on this coefficient model, and every
coefficient transport with the identity on `C`.  Every identity involving
only the carrier survives on the first tensor factor, and every pairing or
translation identity survives on the second, while the coefficient target
still has twice the source dimension.

Therefore the separated union of

1. finite `S3/S4` carrier identities, even with invertible scalar channel
   matrices; and
2. Leavitt pairing/translation identities on an independent coefficient
   factor

cannot imply same-orbit or same-scale multiplicity closure.  A successful
atlas decoder must use an actual quotient relation in which a nontrivial
finite carrier coefficient and the multiplicity transport occur in the same
operator equation.
