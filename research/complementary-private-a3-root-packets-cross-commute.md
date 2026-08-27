---
rg: 2
id: complementary-private-a3-root-packets-cross-commute
kind: claim
title: Complementary private A3 root packets cross-commute before completeness
artifacts:
  - research/complementary-private-a3-cross-commutation-proof.md
distinct_from:
  complementary-private-weyl-loops-have-s3-square-gauge-model: that starts with the completed branch outputs `P_i,R_i,V_i` and derives their loops with the native constant Weyl; this proves coefficient orthogonality for every individual depth-two private arm and genuine reverse at arbitrary EL20 root positions before either output is formed.
  complementary-depth-two-a3-whiteheads-have-a6-gauge-model: that couples the two completed outputs through `q_0+q_1=1`; this shows that no direct cross-channel root interaction between the uncompleted private packets can supply an additional coupling.
  depth-two-a3-private-whiteheads-have-finite-gl6-model: that fences one depth-two A3 packet and its private Whiteheads; this treats the interaction of two complementary top-prefix packets and includes explicit shared-index reverse-arm/output cells.
---

**ESTABLISHED CROSS-CHANNEL FENCE.**  For `i in {0,1}` let

```text
M_i={s_(i mu)t_(i nu): mu,nu are binary words}.       (CAC1)
```

Only the displayed finite subset of `(CAC1)` is needed.  The depth-two A3
coefficients and their genuine reverses are

```text
a_i=s_i t_(i0),             a_i^-=s_(i0)t_i,
b_i=s_(i0)t_(i1),           b_i^-=s_(i1)t_(i0),
c_i=s_(i1)t_i,              c_i^-=s_i t_(i1),         (CAC2)
```

and the branch output coefficient `q_i=s_it_i` is in the same packet.
Every coefficient in `(CAC2)` belongs to `M_i`.

The leading prefixes `0` and `1` are incomparable.  Hence prefix
cancellation gives

```text
r_0 r_1=0=r_1 r_0             for r_i in M_i.         (CAC3)
```

Consequently elementary root operators with coefficients from opposite
packets commute at **all** root positions, including composable and opposite
positions.  Two smallest literal shared-index examples inside EL20 are

```text
[x_(10,7)(a_0^-), x_(7,12)(a_1)]
 =x_(10,12)(a_0^- a_1)=1,                             (CAC4)

[x_78(q_1), x_(8,10)(c_0^-)]
 =x_(7,10)(q_1 c_0^-)=1.                              (CAC5)
```

The first puts a genuine branch-zero opposite arm against a branch-one
private arm.  The second puts the same kind of opposite arm against the
actual branch-one output.  The reverse coefficient products vanish as
well.  Thus an exact two-by-two multiplication proves commutation even when
the two root positions are opposite rather than merely composable.

More generally every word formed solely from branch-zero private roots and
their reverses commutes factor by factor with every such branch-one word.
In particular, adding all direct cross-channel private-arm/opposite-root
relations supplies no nonlinear relation beyond commutation.  The first
ordinary relation that couples the packets is still the additive
completeness fusion

```text
P_0P_1=x_78(q_0+q_1)=x_78(1),                         (CAC6)
```

already fenced by the complementary output claims.

This also gives an exact finite gauge fence.  The private arms do not
individually reduce the signed-Hecke reservoir, so `(CAC3)` creates no new
private-arm reservoir symbol.  For the completed branch-resolved letters,
the `S_3 times S_3` model of
`complementary-private-weyl-loops-have-s3-square-gauge-model` places branch
zero in the first factor and branch one in the second.  It therefore
realizes every cross-commutation that can survive to that interface.  The
native gauges remain diagonal,

```text
D=(c,c),                 E=(a,a),                     (CAC7)
```

and `DE=(ca,ca)` still has order three.  Therefore neither `(CAC4)` nor
`(CAC5)`, nor the full family `(CAC3)`, gives a new same-chart equation
involving native `D,E`.

This is a scoped algebraic and reservoir-gauge fence, not a finite
representation of the whole EL20 presentation.  A successful cross-channel
cell must first leave the two orthogonal top-prefix components--for example
by using a genuinely mixed coefficient `s_(0 mu)t_(1 nu)` or by applying
completeness before the noncommuting occurrence.  It cannot be made from
one pure private arm from each complementary A3 packet.

No Property T, Kazhdan input, local computation, trace hypothesis, or
literature theorem is used.

DERIVATION
complementary-private-a3-cross-commutation-proof
