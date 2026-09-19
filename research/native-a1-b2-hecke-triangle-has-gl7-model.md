---
rg: 2
id: native-a1-b2-hecke-triangle-has-gl7-model
kind: claim
title: The native A1-B2 Hecke triangle still has a marked GL7 model
artifacts:
  - research/native-a1-b2-hecke-triangle-gl7-proof.md
  - experiments/native_a1_b2_hecke_triangle_gl7_audit.py
distinct_from:
  literal-prefix-coupling-of-j1-j2-has-gl7-model: that authenticates both adjacent prefix Whiteheads and their braid but does not attach either actor to a center-chain Hecke triangle; this attaches J1 to the literal A1 and B2 occurrences through already named t0 and s00 arms.
  native-whitehead-hecke-head-has-order-seven-anchor: that proves the abstract order-seven relation in the elementary Leavitt group and its sensitivity to a commuting spectator sign; this places the literal triangle inside the current finite GL7 chart after both native actor signs have already been removed.
  center-chain-common-source-authenticates-native-covariances: that asks for a positive representation-dependent subcorner identifying both unequal Hecke rows with the native selector covariances; this types only the first exact Hecke triangle and retains a finite marked model.
---

**ESTABLISHED FIRST-HECKE-TRIANGLE FENCE.**  Retain the literal first
prefix actor

```text
J_1=X_1Y_1X_1,
X_1=x_87(s_00t_0),       Y_1=x_78(s_0t_00),           (ABH1)
```

from the coupled `J_1,J_2` packet.  The first returned-root diamond already
contains the named occurrences

```text
T_0=x_97(t_0),           S_00=x_89(s_00).
```

Adjoin the two literal inverse-prefix arms

```text
S_1=x_49(s_1),           T_1=x_94(t_1).
```

Ordinary nonopposite Steinberg commutators then compile the actual
center-chain arms

```text
A_1=[S_1,T_0]=x_47(s_1t_0),
B_2=[S_00,T_1]=x_84(s_00t_1),                         (ABH2)
```

and their shared triangle closes on the already authenticated factor:

```text
[B_2,A_1]=x_87(s_00t_1s_1t_0)=X_1.                  (ABH3)
```

Thus this is the native coefficient occurrence, not an analytic
replacement.  The exact Hecke-head relation is

```text
(J_1B_2A_1)^7=1.                                    (ABH4)
```

Nevertheless `(ABH1)--(ABH4)` have an exact marked model in the same
`GL_7(F_2)` chart.  On the vertex order

```text
(7_0,9,8_0,7_1,10,8_1,6)
```

keep `J_1=(7_0 8_0)`, and assign

```text
T_0=e_(9,7_0),       S_00=e_(8_0,9),
S_1=e_(6,9),         T_1=e_(9,6),
A_1=e_(6,7_0),       B_2=e_(8_0,6).                 (ABH5)
```

Both rows in `(ABH2)` and `(ABH3)` are elementary path commutators.  On
the three vertices `(6,7_0,8_0)`, the packet `(A_1,B_2,J_1)` is the
natural `GL_3(F_2)` packet, so `J_1B_2A_1` has exact order seven.  The
second-branch marked child `e_(7_1,8_1)` remains nonidentity.

Therefore authenticating the first native center-chain triangle does not
yet impose the unequal quarter/eighth Hecke carrier ranks.  A live next row
must couple this first triangle to the second Hecke triangle on one typed
positive carrier, or introduce a coefficient relation incompatible with
the finite `GL_7` specialization.  The first order-seven head alone is
still below the finite-model firewall.

This is a scoped model of the displayed ordinary-root occurrence table,
not a representation of the full binary Leavitt elementary group.  No
Property T, Kazhdan input, literature theorem, local computation, trace
hypothesis, or Lean compilation is used.

DERIVATION
native-a1-b2-hecke-triangle-gl7-proof

