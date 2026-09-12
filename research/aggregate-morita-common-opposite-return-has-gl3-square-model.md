---
rg: 2
id: aggregate-morita-common-opposite-return-has-gl3-square-model
kind: claim
title: The common opposite return breaks the dihedral square but has an exact GL3 square model
artifacts:
  - research/aggregate-morita-common-opposite-return-gl3-square-proof.md
  - experiments/aggregate_morita_returned_opposite_fold_audit.py
distinct_from:
  aggregate-morita-row-column-fold-has-d8-square-model: that stops after the positive-root aggregate fold and leaves the child outputs central in two private dihedral factors; this adds one literal common reverse root, returns both native arms through it, and puts each positive child output opposite its returned reverse child on the same packet.
  aggregate-binary-whitehead-does-not-read-completeness: that factors a row-column Whitehead before the range sum is used; both the positive and reverse parent outputs here are formed by the two completeness children.
  native-opposite-arm-return-has-finite-s6-model: that authenticates only one child arm inside an opposite-root cell; this uses one common reverse parent occurrence to return both children simultaneously.
  full-completeness-opposite-menu-has-finite-gl5-fusion: that transports private opposite-root packets among three fused charts; this is the smaller literal three-coordinate return obtained directly from the aggregate Morita fold.
---

**ESTABLISHED COMMON-OPPOSITE FENCE.**  Retain the aggregate Morita cell

```text
S_0=x_79(s_0),       S_1=x_(7,10)(s_1),
T_0=x_98(t_0),       T_1=x_(10,8)(t_1),
C_i=[S_i,T_i]=x_78(q_i),
N=C_0C_1=x_78(1).                                      (ACR1)
```

The smallest literal opposite-root continuation is the common reverse
parent

```text
D=x_87(1).                                               (ACR2)
```

Return the two native arms through this one occurrence:

```text
U_i=[D,S_i]=x_(8,k_i)(s_i),
V_i=[T_i,D]=x_(k_i,7)(t_i),
R_i=[U_i,V_i]=x_87(s_it_i)=x_87(q_i),                  (ACR3)
```

where `k_0=9` and `k_1=10`.  Completeness now appears a second time:

```text
R_0R_1=x_87(q_0+q_1)=x_87(1)=D.                        (ACR4)
```

Each `R_i` is a literal opposite-root child of `C_i`, and the crossed child
pairs commute.  More importantly, the aggregate parents are the full roots
`N=x_78(1)` and `D=x_87(1)`, so their ordinary Whitehead relation is

```text
NDN=DND.                                                 (ACR5)
```

This genuinely couples the two directions `C_0,C_1` to returned opposite
payloads on the marked occurrence.  It also destroys the old `D_8 times
D_8` countermodel.  In one old dihedral factor, a component `d` of `D`
would have to satisfy

```text
d=[[d,a],[b,d]].                                        (ACR6)
```

Exhaustion of the eight elements gives only `d=1`; then `(ACR5)` forces the
nontrivial parent `N` to be trivial.

The stronger table nevertheless has an exact finite marked model.  Let

```text
K=GL_3(F_2)
```

on coordinate order `(7,k_i,8)`.  In the `i`th copy of `K`, assign

```text
S_i -> x_12(1),       T_i -> x_23(1),
C_i -> x_13(1),       R_i -> x_31(1),
U_i -> x_32(1),       V_i -> x_21(1).                  (ACR7)
```

Put branch-zero names in the first factor of `K times K`, branch-one names
in the second, and set

```text
N=(x_13(1),x_13(1)),
D=(x_31(1),x_31(1)).                                   (ACR8)
```

Every relation `(ACR1)--(ACR5)` and every matching and crossed child
commutator holds exactly.  The marked child

```text
C_1=(1,x_13(1)) != 1.                                  (ACR9)
```

Hence the left regular representation of the finite group `K times K`
has zero defect on this first common-opposite returned table and keeps the
prescribed marked output nontrivial.  The new occurrence removes the
private central-dihedral escape but only upgrades it to two private
three-coordinate Steinberg packets.  A live next row must mix the two
returned child packets by a coefficient-sensitive occurrence not generated
inside their direct product; another common parent opposite root or its
branchwise Whitehead consequences cannot imply Atomic Morita Return.

This is a scoped occurrence-table model, not a finite representation of the
full binary Leavitt Steinberg group.  No Property `(T)`, Kazhdan input,
stability theorem, trace hypothesis, literature theorem, local computation,
or Lean compilation is used.

DERIVATION
aggregate-morita-common-opposite-return-gl3-square-proof
