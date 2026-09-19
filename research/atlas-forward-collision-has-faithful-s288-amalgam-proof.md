---
rg: 2
id: atlas-forward-collision-has-faithful-s288-amalgam-proof
kind: route
title: Glue the factor-swap A4-square to S3 times C2 over a labeled V4
target: atlas-forward-collision-has-faithful-s288-amalgam
requires:
  - atlas-forward-collision-bass-serre-reduction
---

## The first two vertices inside an order-288 group

Fix `rho=(1 2 3)` and a double transposition `beta` in `A4`.  In

```text
C_0=A4 x A4
```

put

```text
r=(rho,rho),       z=(rho,rho^-1),       b=(beta,beta).       (FA1)
```

Then `r,z` commute and generate `C3 x C3`.  Each of `rho beta` and
`rho^-1 beta` has order three, so

```text
(r^-1 b)^3=(z b)^3=1.
```

Moreover `r z` and `r z^-1` recover the two coordinate `C3` subgroups.
Conjugating the diagonal `b` separately by those coordinate rotations and
multiplying conjugates recovers both coordinate Klein four groups.  Hence

```text
<r,z,b>=A4 x A4=C_0,       |C_0|=144.                (FA2)
```

Let `c` swap the two factors and set

```text
H=(A4 x A4) semidirect <c>,       |H|=288.            (FA3)
```

The diagonal element `r` is fixed, the anti-diagonal element `z` is inverted,
and the diagonal involution `b` is fixed.  Thus

```text
c r c=r,       c z c=z^-1,       [b,c]=1,
<r,z,c> ~= C3 x S3,       |<r,z,c>|=18.              (FA4)
```

So the `F` and `C` vertices of the Bass--Serre reduction embed in `H`, with
their common `A=<r,z>` identified exactly.  Also

```text
V=<b,c> ~= C2 x C2.                                  (FA5)
```

## Adjoin the second S3 without changing either vertex

Let

```text
J=S3 x C2,
```

write `c` for the central generator of its `C2` factor, and choose an
order-three `t` and a reflection `b` in its `S3` factor.  Put

```text
s=b t^-1.
```

Then `s^2=1`, `s t=b`, and `<t,s>=S3`.  The labeled subgroups
`<b,c>` in `H` and `J` are both the same abstract `V4`.

Take the left regular permutation representation of `H` on 288 points and
twenty-four copies of the left regular representation of `J`, also on 288
points.  On restriction to `V` they are

```text
Reg(H)|_V       =72 Reg(V),
24 Reg(J)|_V    =24*3 Reg(V)=72 Reg(V).               (FA6)
```

Hence a bijection of the 288-point sets conjugates the two labeled `V`
actions.  After this conjugation, both `H` and `J` are subgroups of the same
`S_288` and agree elementwise on `b,c`.  Let `Q` be the finite subgroup they
generate.  The embeddings of `H` and `J` remain injective, so the images of
the three original vertices have orders `18,144,6`.

## Collision

Inside `J`, the element `c` is central.  Therefore the collision word becomes

```text
t c s c t^-1 c s t c = t s t^-1 s t.                (FA7)
```

The relation `(s t)^2=1` gives `s t s=t^-1`, hence

```text
t s t^-1 = s t
```

and the right side of `(FA7)` is `s t s t=1`.  Thus all defining relations
of `Gamma` hold in `Q`.  Since the vertex inclusions are faithful, in
particular `b` is a nonidentity involution.

The artifact independently constructs the 144-point regular action of
`A4 x A4`, the factor-swap permutation, and checks the orders

```text
|H|=288, |F|=18, |C|=144, |V|=4, |K|=6,
```

as well as `(FA6)--(FA7)`.  The finite enumeration was run through the MSI
wrapper.
