---
rg: 2
id: group-algebra-coefficient-trace-separates-leavitt-corners
kind: claim
title: The canonical group-algebra trace separates the two Leavitt packet idempotents
invalidates:
  - leavitt-corner-equivalence-gives-one-sided-lift
  - leavitt-counterexample-from-idempotent-equivalence
distinct_from:
  leavitt-multiplicative-trace-floor: that studies traces after evaluating packet words in finite matrix targets; this uses the exact coefficient-of-identity trace on the source group algebra.
  leavitt-e-f-murray-von-neumann-equivalence: that asked for an equivalence between the displayed idempotents; this proves that equivalence is impossible.
artifacts:
  - research/artifacts/leavitt-packet-trace-and-compression-2026-08-24.md
---

**ESTABLISHED.**  Let

```text
S=F_2[L_(F_2)(1,2)^x],
e=[g]+[g^2],
f=[1]+[u]+[v]+[g],
```

with `H=<u,v> congruent S_3` and `g=uv` as in
`leavitt-primitive-corner-recursive-extension`.  Then `e` and `f` are not
Murray--von Neumann equivalent in `S`.

Let `tau:S->F_2` be coefficient of the identity.  For finite sums
`a=sum a_r[r]` and `b=sum b_r[r]`,

```text
tau(ab)=sum_r a_r b_(r^(-1))
       =sum_r b_r a_(r^(-1))=tau(ba).                 (LCT1)
```

Thus `tau` is a cyclic additive trace over `F_2`.  The elements `u,v` are
the two distinct generating transpositions of the constant `S_3`, and `g`
and `g^2` are its two nonidentity three-cycles.  Consequently

```text
tau(e)=0,                 tau(f)=1.                    (LCT2)
```

If finite-support elements `x,y in S` satisfied `xy=e` and `yx=f`, cyclicity
would give `0=tau(e)=tau(xy)=tau(yx)=tau(f)=1`, a contradiction.  This
argument does not merely obstruct the proposed corner supports `x in eSf`,
`y in fSe`; it forbids an implementing pair anywhere in `S`.

The augmentation cannot see this distinction because both idempotents have
even support.  The canonical coefficient trace can, because exactly one of
the four basis elements supporting `f` is the identity.  Hence the displayed
strict-corner route to a direct-finiteness counterexample is closed.
