---
rg: 2
id: native-t00-collision-first-hecke-attachment-has-gl10-model
kind: claim
title: The first native Hecke attachment to the paid t00 collision still has a marked GL10 model
artifacts:
  - research/native-t00-collision-first-hecke-gl10-proof.md
  - experiments/native_t00_collision_first_hecke_gl10_audit.py
distinct_from:
  native-t00-y1-collision-pays-marked-opnorm: that forces the collision discrepancy onto at least one sixteenth of the marked active carrier and computes its first contacts with the selector-normalized middle-index dual frame; this attaches the discrepancy to the literal first center-chain Hecke arm and tests whether that contact localizes the paid carrier.
  native-a1-b2-hecke-triangle-has-gl7-model: that authenticates the first Hecke triangle but contains no separated t00 occurrence; this keeps the authenticated triangle and adds the fully paid t00/Y1 discrepancy.
  middle-index-order-seven-orbit-cut-is-native-scale-neutral: that closes all center-chain ejections in a 128-dimensional marked packet whose constant atom erases the scale distinction; this tests only the smallest coefficient-sensitive collision plus one literal Hecke arm and gives a smaller exact occurrence fence.
---

**ESTABLISHED FIRST-ATTACHMENT FENCE.**  Retain

```text
T=x_78(t_00),       Y=x_78(s_0t_00),
d=t_00+s_0t_00,     D=TY=x_78(d)                       (THF1)
```

from `native-t00-y1-collision-pays-marked-opnorm`, and retain the literal
first center-chain Hecke arm

```text
B_2=x_84(b_2),             b_2=s_00t_1                (THF2)
```

from `native-a1-b2-hecke-triangle-has-gl7-model`.  Their ordinary mixed
commutator is

```text
[D,B_2]=x_74(db_2)=x_74(b_0+b_1)=H_0H_1,             (THF3)
H_0=x_74(b_0),       H_1=x_74(b_1),
b_0=t_1,             b_1=s_0t_1.
```

The new root `H_0` has full Leavitt rank scale because `b_0s_1=1`.  This is
the Hecke-position transport of the second identity in `(TYC8)`: it uses the
actual `B_2` occurrence in the native triangle, not an auxiliary dual root.
It does not assert that `D` normalizes the Hecke support or is itself one of
the selector-normalized dual roots.

Nevertheless the whole displayed occurrence packet has an exact marked
model in the same `GL_10(F_2)` chart as
`marked-t00-separation-has-gl10-model`.  On the vertices used there put

```text
Y=e_(7_0,8_0),       T=e_(b,8_0),       D=TY,
B_2=e_(8_0,6),       H_1=e_(7_0,6),     H_0=e_(b,6).  (THF4)
```

Then `(THF3)` is the two elementary length-two paths through `8_0`.  Keep

```text
A_1=e_(6,7_0),       J_1=(7_0 8_0).                  (THF5)
```

The native relation `[B_2,A_1]=X_1` and the exact order-seven relation

```text
(J_1B_2A_1)^7=1                                      (THF6)
```

remain unchanged.  The paid discrepancy `D` is nonidentity, `H_0` is
nonidentity, and the old marked child remains nonidentity.  Thus even the
first literal Hecke attachment can store the ejected full-rank coefficient
as a transverse root-position direction.

This does not contradict the positive payment `(TYC6)`: the finite chart
has no signed-Hecke source projection and imposes no compression of
`P_zP_D` by that projection.  It proves the exact boundary.  A successful
continuation needs a named source reflection or polar-support occurrence
whose ordinary relations force positive intersection with `P_zP_D`; the
mixed commutator with `B_2` alone does not.

This is a scoped elementary occurrence model, not a representation of the
full binary Leavitt elementary group.  No Property T, canonical trace,
literature input, local computation, or Lean compilation is used.

DERIVATION
native-t00-collision-first-hecke-gl10-proof
