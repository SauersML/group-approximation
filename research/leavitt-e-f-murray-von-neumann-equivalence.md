---
rg: 2
id: leavitt-e-f-murray-von-neumann-equivalence
kind: claim
title: The Leavitt order-three corner is equivalent to its primitive subcorner inside the group algebra
distinct_from:
  leavitt-primitive-corner-recursive-extension: that embeds the whole evaluation extension into fSf and proves f<e, but supplies no elements implementing e equivalent to f; this asks for exactly those two finite-support elements.
  leavitt-corner-one-sided-lift-exists: that permits any corner pair whose reverse product has nonidentity evaluation; this pins the reverse product to the explicit primitive idempotent f and is therefore a stronger finite-support target.
  leavitt-matrix-amplification-in-unit-group-algebra: that embeds M_2(S) into eSe with image merely supported by e; it does not prove that e is equivalent to the matrix unit f in S.
artifacts:
  - research/artifacts/leavitt-packet-trace-and-compression-2026-08-24.md
---

In `S=F_2[L_(F_2)(1,2)^x]`, with

```text
e=[g]+[g^2],        f=[1]+[u]+[v]+[g],        f<e,
```

exhibit finite-support elements

```text
x in eSf,        y in fSe,        xy=e,        yx=f.
```

Equivalently, prove `e ~ f` inside `S`.  Since `pi(e)=1` and
`pi(f)=s_0t_0<1`, this is a strictly sharper target than an arbitrary
one-sided inverse: its reverse defect is fixed in advance.

## Attempts

The recursive embedding `lambda:S->fSf` proves only that a copy of `S` is
supported by `f`; it does not produce a Murray--von Neumann equivalence
between `e` and `f`.  Likewise the amplification theorem gives an injection
`M_2(S)->eSe`, not surjectivity onto `eSe`, so matrix units in the image do
not imply this claim.  No implementing pair `(x,y)` and no obstruction to one
is presently known.
