---
rg: 2
id: leavitt-e-f-murray-von-neumann-equivalence
kind: claim
title: The Leavitt order-three corner is equivalent to its primitive subcorner inside the group algebra
refuted_by: group-algebra-coefficient-trace-separates-leavitt-corners
distinct_from:
  leavitt-primitive-corner-recursive-extension: that embeds the whole evaluation extension into fSf and proves f<e, but supplies no elements implementing e equivalent to f; this asks for exactly those two finite-support elements.
  leavitt-corner-one-sided-lift-exists: that permits any corner pair whose reverse product has nonidentity evaluation; this pins the reverse product to the explicit primitive idempotent f and is therefore a stronger finite-support target.
  leavitt-matrix-amplification-in-unit-group-algebra: that embeds M_2(S) into eSe with image merely supported by e; it does not prove that e is equivalent to the matrix unit f in S.
artifacts:
  - research/artifacts/leavitt-packet-trace-and-compression-2026-08-24.md
---

**REFUTED.**  In `S=F_2[L_(F_2)(1,2)^x]`, with

```text
e=[g]+[g^2],        f=[1]+[u]+[v]+[g],        f<e,
```

the former target asked for finite-support elements

```text
x in eSf,        y in fSe,        xy=e,        yx=f.
```

Equivalently, prove `e ~ f` inside `S`.  Since `pi(e)=1` and
`pi(f)=s_0t_0<1`, this is a strictly sharper target than an arbitrary
one-sided inverse: its reverse defect is fixed in advance.

The target is impossible.  The canonical coefficient-of-identity trace is
cyclic on every group algebra, while it takes the values

```text
tau(e)=0,                    tau(f)=1.
```

Here `g,g^2` are the two nonidentity three-cycles in the constant `S_3`,
whereas the support of `f` contains the identity exactly once.  Hence
`xy=e`, `yx=f` would imply `0=tau(xy)=tau(yx)=1`.  The complete argument and
the explicit invalidation edges are recorded in
`group-algebra-coefficient-trace-separates-leavitt-corners`.

## Attempts

The recursive embedding `lambda:S->fSf` proves only that a copy of `S` is
supported by `f`; it does not produce a Murray--von Neumann equivalence
between `e` and `f`.  Likewise the amplification theorem gives an injection
`M_2(S)->eSe`, not surjectivity onto `eSe`, so matrix units in the image do
not imply this claim.  The coefficient trace is the missing obstruction.
