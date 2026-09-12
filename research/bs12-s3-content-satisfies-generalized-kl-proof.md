---
rg: 2
id: bs12-s3-content-satisfies-generalized-kl-proof
kind: route
title: Rewrite the regular S3 cover and expose the residual BS(1,4) HNN relation
target: bs12-s3-content-satisfies-generalized-kl
requires: []
---

Put `a=(123)`, `b=(12)` and use right multiplication on

```text
Q=S3={1,a,a^2,b,ab,a^2b}.
```

Then

```text
a b a^(-1) b^(-1) a=1,
```

so killing the coefficient group and sending `t` to `a`, `s` to `b` gives a
homomorphism of the relative presentation onto `Q`.  Before the one relator
is imposed, its kernel is

```text
D*F7,                    D=*_(h in Q) G_h.
```

This is the usual spanning-tree form of Kurosh/Reidemeister--Schreier.  Write
`X_h` and `Y_h` for the positive `t`- and `s`-edges based at `h`.  Choose the
five tree edges

```text
X_1=X_a=Y_1=Y_a=Y_(a^2)=1
```

and name the seven remaining edges

```text
x=X_(a^2),  u=X_b,  v=X_(a^2b),  z=X_(ab),
p=Y_b,      q=Y_(ab),             r=Y_(a^2b).
```

The lift based at `h` visits

```text
h, ha, hab, haba^(-1), haba^(-1)b, h.
```

Consequently the six exact rewritten relators are

```text
R_1   =g0_1   g1_a   g2_ab    v^(-1) g3_(a^2b) g4_(a^2) x,
R_a   =g0_a   g1_(a^2) g2_(a^2b) u^(-1) g3_b g4_1,
R_a2  =g0_(a^2) x g1_1 g2_b z^(-1) g3_ab g4_a,

R_b   =g0_b u g1_(a^2b) r g2_(a^2) g3_a q^(-1) g4_ab z,
R_ab  =g0_ab z g1_b p g2_1 x^(-1) g3_(a^2) r^(-1)
        g4_(a^2b) v,
R_a2b =g0_(a^2b) v g1_ab q g2_a g3_1 p^(-1) g4_b u.
```

Here `gi_h` denotes `gi` in the copy `G_h`.  The first three relations solve
reversibly for three edge generators:

```text
u=(g3_b g4_1)(g0_a g1_(a^2) g2_(a^2b)),
v=(g3_(a^2b) g4_(a^2)) x (g0_1 g1_a g2_ab),
z=(g3_ab g4_a) g0_(a^2) x (g1_1 g2_b).              (1)
```

For the lower three cells abbreviate

```text
A=g0_b u g1_(a^2b),       B=g2_(a^2) g3_a,
C=g4_ab z,
D0=g0_ab z g1_b,          E=g2_1 x^(-1) g3_(a^2),
F=g4_(a^2b) v,
H=g0_(a^2b) v g1_ab,      J=g2_a g3_1,
I=g4_b u.
```

Then the three relations read

```text
A r B q^(-1) C=1,
D0 p E r^(-1) F=1,
H q J p^(-1) I=1.
```

The first two solve reversibly as

```text
q=C A r B,                r=F D0 p E.
```

Substitution into the last one leaves exactly

```text
K(x) p L(x) p^(-1) I=1,                             (2)
K=H C A F D0,               L=E B J.
```

No coefficient identity has been used: `(1)--(2)` are Tietze moves in the
free product `D*F7`.

Let `B0=D*<x>`.  From `(1)`, each of `v,z` has `x`-exponent sum `1`, while
`u` has sum zero.  Therefore

```text
exp_x(K)=4,                   exp_x(L)=-1.
```

Equation `(2)` is

```text
p L p^(-1)=K^(-1)I^(-1)=:R,
```

and `exp_x(R)=-4`.  The homomorphism `B0 -> Z` which kills `D` and sends
`x` to `1` proves that both `L` and `R` have infinite order.  Hence

```text
<B0,p | p L p^(-1)=R>
```

is the HNN extension identifying the infinite cyclic subgroups `<L>` and
`<R>` by `L^n |-> R^n`.  Britton's lemma embeds `B0`, hence embeds `D`, hence
embeds its distinguished vertex factor `G_1`.  This is the original
coefficient group in the relative presentation and proves the claim.

As a consistency check, if all coefficients are `1`, then `u=1`, `v=z=x`,
so `(2)` becomes

```text
x^4 p x^(-1) p^(-1)=1,
```

the standard `BS(1,4)` presentation for the index-six kernel of
`BS(1,2) -> S3`.
