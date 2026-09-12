---
rg: 2
id: iwahori-mod-p-quotient-proof
kind: route
title: Compare the half-parabolic normal closure with Behr--Mennicke's integral parabolic
target: iwahori-mod-p-quotient-is-psl2
requires:
  - iwahori-square-root-presentation-is-bs14-plus-one-involution
---

In the arithmetic matrices, `u=s^2` is the integral upper unipotent and
`r s r^(-1)=s^4`.  Therefore

```text
u^p=s^(2p) in <<s^p>>,
s^p=r^(-1)s^(4p)r=r^(-1)u^(2p)r in <<u^p>>.
```

The normal closures are equal.  The Behr--Mennicke congruence presentation
identifies the quotient of `SL_2(Z[1/2])` by `<<u^p>>` with `SL_2(F_p)` for
odd `p`; quotienting the two centers identifies the projective quotient with
`PSL_2(F_p)`.  The displayed five-relator presentation is Tietze equivalent
to the arithmetic group presentation, so adjoining `s^p` there gives the
same quotient.
