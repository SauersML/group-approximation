---
rg: 2
id: support-return-gives-gauged-native-loop
kind: claim
title: Support-idempotent returns give an odd native loop with a surviving gauge
artifacts:
  - experiments/support_partial_whitehead_native_return_audit.py
  - research/support-return-native-loop-proof.md
distinct_from:
  minimal-t00-conversion-cannot-return-native-whitehead-root: that excludes return by signed `L_0`; this uses a nonconstant support-idempotent partial Whitehead and obtains exact native reverse-root returns.
  external-group-misses-native-t00-roots: that closes every constant external-return word; this crosses the fence with the prefix projections `e_0,e_000` and records the resulting odd native identities.
  same-center-whitehead-native-selector-subcorner-attachment: that asks for the unequal quarter/eighth selector rows on one positive subcorner; this produces an odd literal `J_i` identity on the recentered carrier but does not preserve the signed Hecke cut carrying those unequal scales.
---

**ESTABLISHED POSITIVE ODD LOOP WITH GAUGE FENCE.**  Retain

```text
Z_1=[B_2,[A_1,N_9]]=x_89(x_1),
Z_2=[[N_9,B_3],A_2]=x_78(x_2),
T=x_97(t_00).                                           (SRL1)
```

The two minimal coefficient conversions are

```text
H_2=[Z_1,T]=x_87(y_2),
H_1=[T,Z_2]=x_98(y_1).                                  (SRL2)
```

Put

```text
W_1=W_79(e_0,e_0),       W_2=W_79(e_000,e_000).        (SRL3)
```

The support identities

```text
x_1e_0=x_1,       e_0y_1=y_1,
e_000x_2=x_2,     y_2e_000=y_2                         (SRL4)
```

give the exact partial-Whitehead returns

```text
W_1Z_1W_1=x_87(x_1),       W_1H_1W_1=x_78(y_1),
W_2Z_2W_2=x_98(x_2),       W_2H_2W_2=x_89(y_2).        (SRL5)
```

Consequently the two full native Whiteheads have the odd literal
factorizations

```text
J_1=W_1(Z_1H_1Z_1)W_1,
J_2=W_2(Z_2H_2Z_2)W_2.                                  (SRL6)
```

This is a genuine improvement over the constant-return fences: each row of
`(SRL6)` contains one literal native `J_i` on the left and no `J_i` on the
right.  Moreover every factor uses actor indices `2,4,5,6,7,8,9`, disjoint
from the recentered roots `z=x_13(q)` and `C=x_(18,19)(q)`.  Hence every
factor commutes with their spectral projections and `(SRL6)` holds on the
same recentered carrier `F=P_zP_C`.

It does not yet attach the unequal selector scales.  Let `E` be the
`128`-element extraspecial Pauli group generated on `F` by
`(A_1,A_2,A_3,B_1,B_2,B_3)`.  Exact conjugation gives the following
membership table, with `1` meaning that the image remains in `E`:

```text
                 A1 A2 A3 B1 B2 B3
W_1               0  1  0  0  1  0
W_2               0  1  0  0  1  0
Z_1H_1Z_1          1  0  0  1  0  0
Z_2H_2Z_2          0  0  1  0  0  1
J_1,J_2            1  1  1  1  1  1.                 (SRL7)
```

For example, `W_1` sends `A_1=x_47(a_1)` to `x_49(a_1)`, not to the
named `A_3=x_49(a_3)`.  The projection `e_000` makes the corresponding
`W_2` image split into its supported and complementary coefficient pieces;
it is not an internal three-qubit control.  Thus neither `W_i` normalizes
the fixed `M_8(C)` label packet and neither has a label negative fraction
there.  The prefix depths `e_0,e_000` do not become profile-independent
quarter/eighth label cuts.

Instead, `W_i` identifies `E` with a different Pauli chart
`E_i=W_iEW_i`.  The inner cross-depth Whitehead normalizes `E_i`, and by
`(SRL6)` its label action on that chart is conjugate to the ordinary
adjacent swap `J_i`.  It is therefore nonidentity and has the same
one-quarter swap label on its own chart, not the desired one-eighth label.
The complete multiplicity content is only the two-chart equation

```text
D_i=w_i h_i w_i^(-1),                                  (SRL8)
```

where `w_i` is the arbitrary chart-transporter gauge.  A finite groupoid
model retains it even together with the native order-seven head.  Use the
natural `GL_3(F_2)` label packet with `(D_iv_i)^7=1`, take a second copy as
the chart `E_i`, and tensor the transporter by an independent central
`C_2`.  Define `h_i=w_i^(-1)D_iw_i`.  All chart covariance, `(SRL8)`, and
the order-seven row hold exactly, while the central transporter spectator
is nontrivial and invisible because it occurs once in each direction.

Exact full-signature tests also show that none of `W_1,W_2`, the four
individual native factors in `(SRL5)`, or `J_1,J_2` preserves the source
signed Hecke cut `Q`.  Thus the odd native occurrence is explicit and
same-carrier on `F`, but it transfers the Whitehead gauge through an
untyped alternate chart rather than eliminating it.  The next necessary
relation must identify that chart with the unequal-scale selector chart.

No Property T, Kazhdan input, trace hypothesis, literature theorem, local
computation, or Lean compilation is used.

DERIVATION
support-return-native-loop-proof
