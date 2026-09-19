---
rg: 2
id: two-positive-cross-fusions-leave-selector-seam
kind: claim
title: Two complementary positive cross fusions leave the native selector seam
artifacts:
  - research/two-positive-cross-fusion-carrier-audit-proof.md
distinct_from:
  fused-cross-returns-cancel-positive-l0-gauge: that correctly identifies the two returned output actions on the signed Hecke carrier; this adds the complementary positive input fusion and keeps track of the different carrier on which its factors occur.
  dyadic-cross-whitehead-fusion-has-finite-product-gauge: that refines each cross Whitehead into suffix-private factors; this uses the two coarse complementary return cells at `k=6` and the aggregate cross Whitehead `K_0K_1`.
  same-center-whitehead-native-selector-subcorner-attachment: that asks for the actual depth-one and depth-two native selector rows on one positive model-dependent subcorner; this proves that the two positive coarse return fusions do not supply that attachment.
---

**ESTABLISHED TWO-CELL CARRIER FENCE.**  Fix `k=6`, put
`T=K_0K_1=w_78(u)` with `u=p+r`, and name the two complementary return
cells

```text
A_0=x_86(r),       A_1=x_86(p),
B_0=x_76(q_0),     B_1=x_76(q_1),                     (TPF1)

C_0=x_86(q_1),     C_1=x_86(q_0),
E_0=x_76(p),       E_1=x_76(r).                       (TPF2)
```

The exact cross returns and fusions are

```text
K_0A_0K_0=B_0,       K_1A_1K_1=B_1,
B_0B_1=x_76(1),                                      (TPF3)

K_0C_0K_0=E_0,       K_1C_1K_1=E_1,
C_0C_1=x_86(1).                                      (TPF4)
```

Both constant roots in `(TPF3)--(TPF4)` are positive-character generators
of `L_0`.  The first positivity is typed on the signed Hecke carrier `Q`,
and each `B_i` preserves `Q`.  Hence

```text
B_0Q=B_1Q.                                            (TPF5)
```

The complementary cross Whitehead commutes with the relevant branch root,
so the first two returns also read `TA_iT=B_i`.  Therefore `(TPF5)`
transports to a genuine equality of the `r`- and `p`-input actions on the
common moved carrier

```text
Q_T=TQT,                 A_0Q_T=A_1Q_T.               (TPF6)
```

The equality in `(TPF5)` also makes the relative two-path loop exactly
computable, but it produces no new label bridge.  Put

```text
Q_i=K_iQK_i,       L_i=K_iA_i:Q_iH -> QH,
P=L_1^(-1)L_0:Q_0H -> Q_1H.                           (TPF6a)
```

The direct path `T` has the same source and range.  Their relative word is

```text
B=T^(-1)P=TA_1TA_0=B_1A_0
 =x_76(q_1)x_86(r).                                   (TPF6b)
```

This cancellation is well typed, but it cancels the label action as well
as the return gauge.  The word `K_0` commutes with `B_1`, and
`K_0A_0K_0=B_0`, so

```text
K_0BK_0=B_1B_0=x_76(1),
B=K_0x_76(1)K_0,             BQ_0=Q_0.                (TPF6c)
```

Consequently `P|_(Q_0H)=T|_(Q_0H)`.  The two paths agree completely; their
relative loop is the identity on its whole source, not an ungauged
nontrivial selector movement.

The second positive fusion does **not** give the analogous equality on
`Q_T`.  Its positivity says `x_86(1)Q=Q`, whereas the individual input
occurrences in `(TPF4)` are typed on the moved `K_i` cuts.  In particular,

```text
T x_86(1) T=x_76(u),                                  (TPF7)
```

so its action on `Q_T` is conjugate to the uncontrolled action of
`x_76(u)` on `Q`, not to the positive identity action on `Q`.  The chart
movement is genuine: for `h=x_28(1)` in `L_0`,

```text
T h T=x_27(u) notin L_0.                              (TPF8)
```

Thus `T` does not normalize the signed pair and the `Q` and `Q_T` typings
cannot be silently identified.

Even after forgetting this carrier distinction, the displayed occurrence
equations do not force an individual `K_i` gauge.  In the exact scoped
finite model

```text
G=C_2 times C_2=<d_0,d_1>,
K_0 |-> d_0,       K_1 |-> d_1,       T |-> d_0d_1,  (TPF9)
```

assign every named branch-root reservoir factor in `(TPF1)--(TPF4)` to the
identity.  All involution, commutation, conjugation, fusion, and product
rows hold, while `d_0,d_1`, and `d_0d_1` are nontrivial.  This is a scoped
model of the displayed reservoir equations, not a finite representation of
the full elementary group.

Finally, the shared coefficients in `(TPF6)` are only the inverse
depth-one pair

```text
r=a_1=s_1t_0,                  p=b_1=s_0t_1.          (TPF10)
```

The unequal native selector transports instead use

```text
x_1=b_2a_1=s_(00)t_0,          x_2=b_3a_2=s_(000)t_(00),
```

in the literal root occurrences `x_87(x_1)` and `x_98(x_2)`.  Neither
`J_i` nor `v_i` occurs in `(TPF1)--(TPF4)`, and every `K_i` occurs twice.
Consequently `(TPF5)--(TPF6)` does not establish the open unequal-scale
native selector attachment.

There is also no gauge-name retyping shortcut.  The common action in
`(TPF5)` is the full restriction of the literal roots `B_i` to `QH`.  It is
not the `V_i` factor of a literal `J_i` on the same-center `M_8` carrier,
nor the `E_i` factor of `v_i` on the recentered `M_32` carrier.  Moreover
`(IKT5)` gives

```text
J_1^(-1)K_i notin Norm(L_0,lambda_0),
```

so even the `K_i` cuts cannot be retyped as the first native Whitehead
target.  Taking the direct product of `(TPF9)` with the established finite
native actor-holonomy model leaves all `J_i,v_i` reservoir factors
nontrivial while preserving the two-cell table.  Thus the existing
relations impose no identification between these literal occurrences.

The smallest missing carrier row is a positive model-dependent subcorner
on which the **same literal** `x_86(1)` occurrence has synchronized `Q` and
`Q_T` actions, equivalently a controlled overlap which kills the
`x_76(u)` holonomy in `(TPF7)`.  Even after that synchronization, one more
odd depth-changing occurrence must attach the shared `r,p` action to one of
the actual `x_1,x_2` selector rows.  The relative loop `(TPF6b)` cannot
supply it because `(TPF6c)` makes that loop the identity on its source.  No
Property T, Kazhdan input, trace profile, literature theorem, local
computation, or Lean compilation is used.

DERIVATION
two-positive-cross-fusion-carrier-audit-proof
