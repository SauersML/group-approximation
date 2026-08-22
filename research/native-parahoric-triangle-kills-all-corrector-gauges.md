---
rg: 2
id: native-parahoric-triangle-kills-all-corrector-gauges
kind: claim
title: The native parahoric triangle kills every common-carrier corrector gauge
distinct_from:
  actual-parahoric-triangle-kills-abelian-correctors: that uses a forty-two-point unimodular relation certificate and robustly kills commuting or almost-commuting atlas gauges; this uses two lower-root translations and cancellation to kill an arbitrary nonabelian gauge on one common carrier.
  rank-two-weyl-triangle-is-first-apartment-gauge-detector: that proves collapse after the corrector is already known to commute with the whole finite root packet; this needs only four explicit parahoric root invariances and does not assume correctors commute with one another or with the whole packet.
  periodic-conductor-plateaux-pay-a-shared-root-seam: that rules out block-diagonal flat plateaux at the shared-root seam; this proves the exact and quantitative collapse after the seam has supplied one common supported corrector.
---

Let

```text
C=SL_3(Z),
h=diag(2,1,1/2),
D=C cap hCh^-1.                                        (NPC1)
```

Write `x_ij(t)=I+tE_ij` and let `a=n_12`, `b=n_23` be the signed simple-Weyl
root words.  Let `C` act by automorphisms on an arbitrary group `K`, and let
`z in K`.  Assume

```text
d.z=z                 for every d in D,
z=(a.z)(b.z).                                             (NPC2)
```

Then

```text
z=1.                                                       (NPC3)
```

No commutativity, linearity, finiteness, or trace is assumed for `K`.

## Two translate-and-cancel moves

Put `d_2=x_32(1)`.  Both

```text
d_2 in D,
a^-1 d_2 a=x_31(plusOrMinus 1) in D.                    (NPC4)
```

Thus `d_2` fixes both `z` and `a.z`.  Translate the ordered product in
`(NPC2)` by `d_2` and compare it with `(NPC2)`:

```text
(a.z)(b.z)=z=d_2.z=(a.z) d_2.(b.z).                    (NPC5)
```

Left cancellation shows that `d_2` fixes `b.z`.  Equivalently,

```text
b^-1 d_2 b=x_23(plusOrMinus 1)                          (NPC6)
```

fixes `z`.

Similarly put `d_1=x_21(1)`.  We have

```text
d_1 in D,
b^-1 d_1 b=x_31(plusOrMinus 1) in D.                    (NPC7)
```

Now `d_1` fixes `z` and `b.z`.  Comparing the translated triangle and using
right cancellation shows that `d_1` fixes `a.z`; hence

```text
a^-1 d_1 a=x_12(plusOrMinus 1)                          (NPC8)
```

fixes `z`.

The subgroup `D` already contains `x_21(1)` and `x_32(1)`.  Together with
`(NPC6)` and `(NPC8)`, these are the four elementary simple-root generators
of `SL_3(Z)`.  Therefore all of `C`, in particular `a` and `b`, fixes `z`.
The triangle becomes `z=z^2`, so cancellation gives `(NPC3)`.  Reversing the
order of the two triangle factors gives the same conclusion after exchanging
the two cancellation steps.

## Dimension-free normalized-HS form

Let now `rho:C->U(m)` be an exact unitary representation and

```text
alpha_g(T)=rho(g)T rho(g)^*.                             (NPC9)
```

For a unitary `Z`, define

```text
epsilon_tri=||Z-alpha_a(Z)alpha_b(Z)||_2,               (NPC10)
epsilon_D=max ||alpha_d(Z)-Z||_2,                       (NPC11)
```

where the maximum in `(NPC11)` is over the fixed four lower-root words

```text
x_21(1), x_32(1), a^-1 x_32(1)a, b^-1 x_21(1)b.         (NPC12)
```

The approximate version of `(NPC5)`, using bi-invariance and the triangle
once before and once after applying `alpha_(d_2)`, gives

```text
||alpha_(x_23(plusOrMinus 1))(Z)-Z||_2
 <=2 epsilon_tri+2 epsilon_D.                           (NPC13)
```

The other cancellation gives the same bound for `x_12(plusOrMinus 1)`.
Telescoping the three-root words for `a` and `b` therefore gives

```text
||alpha_a(Z)-Z||_2,
||alpha_b(Z)-Z||_2 <=4 epsilon_tri+5 epsilon_D.          (NPC14)
```

Finally

```text
||Z-I||_2=||Z^2-Z||_2
 <=9 epsilon_tri+10 epsilon_D.                          (NPC15)
```

For an approximate actor representation, the same proof adds a fixed
constant times the defects of the finitely many multiplication and
conjugation words occurring in `(NPC4)--(NPC14)`.  The constant is
independent of matrix dimension, multiplicity, conductor depth, and any
period used to recover the local root packet.

Thus there is no residual perfect or nonsolvable **common-carrier** gauge.
Once supported chamber transitions have been decoded on one carrier, the
native parahoric/root words collapse their correction factor with a fixed HS
modulus.  The remaining arithmetic decoder problem is exactly prior to this
endpoint: prove that the six rounded chamber packets share such a carrier,
or charge failure to rectangular conductor leakage.

The common-carrier hypothesis is necessary, not merely an artifact of this
proof.  In `affine-weyl-folner-cut-survives-native-parahoric-triangle`, the
six denominator/Weyl actions have a joint trace-`1/42` Folner cutoff while
the native triangle holds exactly on a trivial corrector in the same
abelian ambient algebra.  The triangle becomes coercive only after a raw
incidence relation authenticates the cutoff as the source/range of its
factors.
