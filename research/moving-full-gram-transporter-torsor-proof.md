---
rg: 2
id: moving-full-gram-transporter-torsor-proof
kind: route
title: Divide an arbitrary moving transporter by the known Whitehead and test the shortest opposite root
target: one-nonnormal-dressing-cannot-preserve-moving-full-gram
requires:
  - literal-whiteheads-give-gauged-moving-bridge-table
  - fano-semidir-bridges-are-wrong-subgroup-or-gauged
---

If `wQw^(-1)=JQJ^(-1)`, then

```text
(J^(-1)w)Q(J^(-1)w)^(-1)=Q,
```

so `J^(-1)w in Norm(Q)` and `w in J Norm(Q)`.  Conversely every
`w=Jn`, `n in Norm(Q)`, satisfies the required equality.  The right-torsor
description follows similarly by using `wJ^(-1) in Norm(Q')`.  This proves
`(OND1)` and the two dressing criteria.

For the explicit check, on the ordered basis `(e_2,e_8)` one has

```text
d=[[1,1],[0,1]],             y=[[1,0],[1,1]],
```

and `y^(-1)=y`.  Direct multiplication gives `(OND3)`.  The directed
generators of `L_0` have sources

```text
6,5,4,8,9,9,9,5,6,6,
```

never `2`; hence each fixes `e_2`, and so does all of `L_0`.  But `(OND3)`
sends `e_2` to `e_8`.  Thus `y` does not normalize `L_0`.  Equality
`yQy^(-1)=Q` would force equality of the group-algebra supports
`yL_0y^(-1)=L_0`, which is impossible.  Applying the torsor identity proves
the claimed full-Gram failure.
