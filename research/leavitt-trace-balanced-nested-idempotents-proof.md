---
rg: 2
id: leavitt-trace-balanced-nested-idempotents-proof
kind: route
title: Localize a cubic unit on a proper Leavitt corner and pair inverse conjugacy classes
target: leavitt-trace-balanced-nested-idempotents
requires:
  - leavitt-corner-idempotent-unital-surjection
artifacts:
  - research/artifacts/kaplansky-cross-atlas-affine-lift-2026-09-07.md
---

Use the self-similarity `R ~= M_2(R)`.  In `M_2(R)` put

```text
G = [[0,1],[1,1]].                                      (1)
```

Then `G^2+G+I=0`, so `G^3=I` and `G+G^(-1)=I`.  This is the
matrix form of the order-three unit in
`leavitt-corner-idempotent-unital-surjection`.

Choose a nonzero proper idempotent `q` of `R`, for example `q=s_0t_0`, and
put

```text
P=diag(q,q),                 H=P G+(I-P).                (2)
```

The scalar diagonal `P` commutes with `G`.  Orthogonality of `P` and `I-P`
therefore gives

```text
H^3=P G^3+(I-P)=I,
H+H^2=P(G+G^2)+2(I-P)=P.                                (3)
```

Both corners of `P` are nonzero, so `H` is neither `I`, `G`, nor `G^2`.
Thus `G,H` are independent commuting elements of order three and generate
`C_3 x C_3`.  Transport `(G,H,P)` through `M_2(R)~=R`, calling their images
`g,h,p`.  This proves `(TBN1)`.

In `S=F_2[Q]`, an order-three element `u` satisfies

```text
([u]+[u^(-1)])^2=[u^2]+2[1]+[u^(-2)]
                  =[u^(-1)]+[u].                        (4)
```

Hence `e` and `c` are commuting idempotents, and `f=ec` is an idempotent
with `ef=fe=f`.  Evaluation and `(TBN1)` give

```text
pi(e)=1,              pi(c)=p,              pi(f)=p.     (5)
```

Since `p` is nonzero and proper, `(5)` proves `0!=f!=e`.  Independence of
`g,h` shows that the four terms of `f` are distinct.  Thus both `e` and `f`
have even support and augmentation zero.

The quotient images are already equivalent.  With `q=s_0t_0`, put
`T=diag(t_0,t_0)` and `U=diag(s_0,s_0)`.  Then

```text
T U=I,                         U T=P.                    (5a)
```

Transport through `M_2(R)~=R` to obtain a Murray--von Neumann equivalence
between `pi(e)=1` and `pi(f)=p`.

It remains to prove the stronger cocenter statement.  Let

```text
J=[[0,1],[1,0]].                                        (6)
```

Direct multiplication gives `J G J^(-1)=G^2`.  Since `J` commutes with the
scalar diagonal `P`, equations `(2)` and `(6)` also give

```text
J H J^(-1)=H^2.                                         (7)
```

After transport to `Q`, one conjugator therefore simultaneously interchanges
`g` with `g^(-1)` and `h` with `h^(-1)`.  In the cocenter over `F_2`,

```text
[e]=[g]+[g^(-1)]=2[g]=0.                                (8)
```

The four terms of `f` split into two conjugate pairs,

```text
gh       ~ g^(-1)h^(-1),
gh^(-1) ~ g^(-1)h,                                     (9)
```

so each pair occurs twice in its conjugacy-class coordinate.  Hence `[f]=0`
as well.  This proves `(TBN3)--(TBN5)`.

Finally, if `x in eSf`, `y in fSe` satisfy `xy=e`, `yx=f`, then both lie in
`eSe` because `f<=e`.  They are a strict one-sided inverse pair in that
corner.  Padding by `1-e` proves the displayed failure of direct finiteness
in `S`.  QED
