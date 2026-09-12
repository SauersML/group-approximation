---
rg: 2
id: dyadic-cross-whitehead-fusion-has-finite-product-gauge
kind: claim
title: Dyadic refinement of the cross Whiteheads retains a finite product gauge
artifacts:
  - research/dyadic-cross-whitehead-fusion-proof.md
distinct_from:
  cross-branch-partial-whiteheads-have-finite-wreath-gauge-model: that factors the aggregate branch flip into the two coarse cross-branch Whiteheads; this refines each coarse coefficient by the next binary address and tests the coarse-versus-fine fusion equations.
  individual-cross-whiteheads-miss-native-hecke-target: that tests each coarse factor against the native row-one Hecke targets; this computes the refined factors and repeats the native typing test before fusion.
  complementary-private-weyl-loops-have-s3-square-gauge-model: that uses the two diagonal branch idempotents; these are the off-diagonal cross matrix units refined by a private suffix address.
---

**ESTABLISHED DYADIC-FUSION FENCE.**  Refine the cross matrix units by

```text
p_j=s_(0j)t_(1j),        r_j=s_(1j)t_(0j),
e_(ij)=s_(ij)t_(ij),                         j=0,1.  (DCF1)
```

Prefix cancellation and completeness give

```text
p=p_0+p_1,               r=r_0+r_1,
p_jr_k=delta_(jk)e_(0j), r_jp_k=delta_(jk)e_(1j),
p_jp_k=r_jr_k=0.                                      (DCF2)
```

For `W(a,b)=x_78(a)x_87(b)x_78(a)`, put

```text
K_(0,j)=W(p_j,r_j),       K_(1,j)=W(r_j,p_j).         (DCF3)
```

The two suffix packets are orthogonal, so the factors with different `j`
commute.  Their exact two-by-two blocks multiply to

```text
K_0=K_(0,0)K_(0,1),       K_1=K_(1,0)K_(1,1).        (DCF4)
```

Thus coarse-versus-fine equality is a genuine full-Leavitt occurrence
identity.  It is only a fusion identity: it does not make an individual
fine factor preserve the signed Hecke carrier.

Indeed, for the literal `h=x_28(1)` in `L_0`, the second block rows give

```text
K_(0,j)hK_(0,j)=x_27(r_j)x_28(1+e_(1j)),
K_(1,j)hK_(1,j)=x_27(p_j)x_28(1+e_(0j)).              (DCF5)
```

Each image has nonconstant Leavitt entries and hence is outside the
constant group `L_0`.  Nor does the native `J_1` provide the missing target.
Writing `x_1=s_00t_0`, `y_1=s_0t_00`, direct multiplication of its actual
block with the first row of `(DCF5)` gives

```text
(J_1K_(0,j))h(J_1K_(0,j))^(-1)
 =x_27(x_1)
  x_28(1+e_(1j)+e_00+s_(1j)t_jt_00).                 (DCF6)
```

This is again nonconstant.  Consequently no `K_(0,j)` has target `Q` or
`J_1QJ_1^(-1)`.  Since `t_1=J_1v_1` and `v_1` normalizes the signed pair,
the Singer target fails as well.  The analogous `K_(1,j)` rows are also
nonconstant; explicitly, after `J_1` their row coefficients are

```text
j=0: (p_0,1+e_00),          j=1: (p_1+x_1,q_1).       (DCF6b)
```

The literal constant coordinate Weyl does act on the refined words, but
only by the expected moving-chart exchange:

```text
w_78(1)K_(0,j)w_78(1)=K_(1,j).                       (DCF7)
```

The complete fine-fusion gauge equations exposed by `(DCF4)` and `(DCF7)`
have an exact finite model.  In `S_4 times S_4`, set

```text
d=(1 2),       e=(2 3),
b=(1 3)(2 4),  c=dbd=(1 4)(2 3),  a=bc=(1 2)(3 4),

D=(d,d),       E=(e,e),
k_(0,0)=(b,1), k_(0,1)=(1,b),
k_(1,0)=(c,1), k_(1,1)=(1,c).                        (DCF8)
```

Then all fine factors are involutions, all orthogonal-address commutations
hold, `Dk_(0,j)D=k_(1,j)`, and fusion gives

```text
k_0=(b,b),       k_1=(c,c),       k_0k_1=(a,a).      (DCF9)
```

Meanwhile `DE=((1 2 3),(1 2 3))` retains order three.  Repeating one `S_4`
factor per suffix leaf gives the same exact model at every fixed dyadic
depth; a finite permutation of equal-depth addresses can be adjoined as a
finite wreath action without changing the diagonal `D,E` packet.

Therefore dyadic refinement does not turn coarse fusion into an ungauged
selector transport.  A positive ESB occurrence must couple two different
suffix leaves before their sum is taken and return one of the nonconstant
cuts in `(DCF5)` to a native Hecke target; the parent equality `(DCF4)` alone
only multiplies their independent finite gauges.

No Property T, Kazhdan input, trace hypothesis, literature theorem, local
computation, or Lean compilation is used.

DERIVATION
dyadic-cross-whitehead-fusion-proof
