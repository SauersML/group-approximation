---
rg: 2
id: reverse-return-has-native-arm-leavitt-diamond
kind: claim
title: Each reverse-root spectator return has a coefficient-sensitive diamond through both literal native arms
artifacts:
  - experiments/reverse_return_native_arm_diamond_audit.py
  - research/reverse-return-native-arm-leavitt-diamond-proof.md
distinct_from:
  reverse-mixed-root-has-two-positive-hecke-commutator-returns: that obtains the two constant spectator returns from the actual mixed-braid reverse root using positive signed-Hecke roots; this attaches each returned occurrence to both non-Boolean native arms in its row.
  eight-external-returns-have-no-whitehead-gauge-lock: that exhausts constant external roots under the native Whitehead/Singer packet; this leaves the constant/Boolean window and uses uncancelled `s_i,t_i` prefix coefficients.
  minimal-t00-conversion-cannot-return-native-whitehead-root: that multiplies a forward native coefficient by `t_00` and searches for a signed-`L_0` conjugator back to one prescribed reverse root; this is a two-sided commutator diamond returning the already authenticated spectator root.
---

**ESTABLISHED COEFFICIENT-SENSITIVE NATIVE OCCURRENCE ATTACHMENT.**  Retain
the literal native rows

```text
A_1=x_47(s_1t_0),       B_2=x_84(s_00t_1),       J_1,
A_2=x_58(s_1t_00),      B_3=x_95(s_000t_1),      J_2.       (RND1)
```

The first spectator return `N_1=x_96(1)` has the exact factorization
diamond

```text
C_1 =[x_94(t_1),A_1]       =x_97(t_0),
D_1 =x_76(s_0),
C'_1=x_98(t_00),
D'_1=[B_2,x_46(s_1)]       =x_86(s_00),

[C_1,D_1]=[C'_1,D'_1]=x_96(1),                         (RND2)
J_1 C_1 J_1=C'_1,             J_1 D_1 J_1=D'_1.       (RND3)
```

The next-prefix row gives the parallel diamond for `N_2=x_27(1)`:

```text
C_2 =[x_25(t_1),A_2]       =x_28(t_00),
D_2 =x_87(s_00),
C'_2=x_29(t_000),
D'_2=[B_3,x_57(s_1)]       =x_97(s_000),

[C_2,D_2]=[C'_2,D'_2]=x_27(1),                         (RND4)
J_2 C_2 J_2=C'_2,             J_2 D_2 J_2=D'_2.       (RND5)
```

Thus the two returns produced from the literal mixed-braid residual are not
confined to the constant or Boolean coefficient windows.  Each has a fixed
ordinary-word continuation containing both literal native arms in its row,
and its Whitehead covariance is an exact equality of those very
occurrences.  The coefficient cancellations use

```text
t_1(s_1t_(0^m))=t_(0^m),        t_(0^m)s_(0^m)=1,      (RND6)
(s_(0^(m+1))t_1)s_1=s_(0^(m+1)).
```

This is a genuine new attachment, but it is not silently promoted to the
same-chart gauge lock.  Equations `(RND3)` and `(RND5)` are simultaneous
covariance of both commutator factors.  Without a reducing occurrence cut
for one of the nonnormal factors, an independent transport gauge can still
be inserted on the target chart and absorbed by both primed factors.  The
next step is therefore sharply typed: authenticate one side of either
diamond on the signed carrier/native cut, or find a second, non-equivariant
return identifying one primed factor on the source chart.  The old
constant-spectator fence no longer rules out this continuation, but the
diamond alone does not finish `(ESB2)`.

No Property `(T)`, Kazhdan input, stability theorem, trace hypothesis,
literature result, local computation, or Lean compilation is used.

DERIVATION
reverse-return-native-arm-leavitt-diamond-proof
