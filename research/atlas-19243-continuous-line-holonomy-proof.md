---
rg: 2
id: atlas-19243-continuous-line-holonomy-proof
kind: route
title: Rewrite with x=cs and balance a dihedral line block by two standard S3 blocks
target: atlas-19243-has-continuous-regular-s3-line-holonomy
requires:
  - atlas-19243-s3-relative-normal-form
---

Substitute `c=xs` into the collision word.  Using
`s r^(-1)=r s`, `s x=x^(-1)s`, and `srs=r^(-1)` reduces it to

```text
r x^2 r x^(-1) r^(-1) x^(-1),
```

which equals one exactly when `r x^2 r=x r x`.  Setting `r=1` makes this
identity tautological, while `sxs=x^(-1)` is the standard presentation of
the infinite dihedral group in terms of a translation and a reflection.

On the line block `(CRH4)`, the original collision word is one for any two
involutions `s,c`, because `r=1` reduces it to
`c s c c s c=1`.  On either standard block, scalar `c=+/-1` occurs four times,
and the remaining word is

```text
r s r^(-1) s r=r(s r^(-1)s)r=r^3=1.
```

This proves the relation blockwise.  The decomposition `(CRH5)` is the
regular character decomposition of `S3`.  A reflection has one positive and
one negative eigenvalue; the two scalar standard blocks contribute two
positive and two negative eigenvalues respectively.  Hence `c` is balanced,
proving the lift statement and the claim.

