---
rg: 2
id: first-native-diamond-extension-of-cross-return-has-gl7-c2-model
kind: claim
title: The first native depth-changing diamond extends the cross return to a finite GL7-C2 model
artifacts:
  - research/first-native-diamond-cross-return-gl7-c2-proof.md
  - experiments/first_native_diamond_cross_return_gl7_c2_audit.py
distinct_from:
  private-middle-swap-crosses-returned-morita-branches-but-has-gl6-model: that closes the depth-one positive and returned cross coefficients in one six-coordinate model; this adjoins the first literal depth-changing native Whitehead diamond sharing one of its returned arms.
  reverse-return-has-native-arm-leavitt-diamond: that establishes the coefficient-sensitive diamond and leaves its transport gauge open; this closes that diamond together with the aggregate cross-return packet in an explicit finite marked model.
  intermediate-native-arm-orbit-cuts-retain-the-return-gauge: that fences spectral cuts made from an order-seven orbit of the native diamond; this is the smaller exact occurrence-table fence before any order-seven actor is adjoined.
---

**ESTABLISHED FIRST DEPTH-CHANGING EXTENSION FENCE.**  Retain the
private-middle cross-return table and its literal returned arm

```text
A=x_97(t_0)=V_0.                                       (NDC1)
```

Add the first native Whitehead `J=J_1` and the other arm of its first
coefficient-sensitive diamond:

```text
B=x_76(s_0),                    M=[A,B]=x_96(1),
A'=JAJ^(-1)=x_98(t_00),
B'=JBJ^(-1)=x_86(s_00),         [A',B']=M.             (NDC2)
```

The coefficient products are exactly

```text
t_0s_0=1,             t_00s_00=1.                     (NDC3)
```

Thus this is not another balanced depth-one actor: it contains the literal
degree-minus-two coefficient `t_00`, the degree-plus-two coefficient
`s_00`, and the actual native depth-one-to-two Whitehead occurrence.  It
also shares `A=V_0` with the common-opposite Morita packet.

Let `H=w_(9,10)(1)` be the private-middle swap.  The supports of `H` and
`J` are disjoint, so

```text
[H,J]=1.                                               (NDC4)
```

Conjugating `(NDC2)` by `H` therefore supplies the entire cross-branch
naturality square on the same occurrences:

```text
[HAH^(-1),HBH^(-1)]=HMH^(-1),
[HA'H^(-1),HB'H^(-1)]=HMH^(-1).                       (NDC5)
```

This is the smallest depth-changing continuation of the six-coordinate
cross return which both shares a returned native arm and is compared under
the cross-branch actor.  It still does not lock the native Whitehead gauge.

Indeed, enlarge the `GL_6(F_2)` model by one vertex `6` and order the
vertices as

```text
(7_0,9,8_0,7_1,10,8_1,6).                            (NDC6)
```

Keep the old six-coordinate matrices, put `e_ab=I+E_ab`, and assign

```text
B=e_(7_0,6),             M=e_(9,6).                   (NDC7)
```

Let `j_0` be the permutation matrix interchanging `7_0,8_0`.  Then

```text
j_0 A j_0^(-1)=e_(9,8_0)=T_0,
j_0 B j_0^(-1)=e_(8_0,6),                             (NDC8)
```

and both commutators in `(NDC2)` are `e_(9,6)`.  The label permutations
`j_0` and `H` have disjoint supports, so `(NDC4)--(NDC5)` hold exactly.

Finally work in

```text
GL_7(F_2) times C_2=<c>
```

and send the literal `J` to `(j_0,c)`, while every other named occurrence
has trivial `C_2` coordinate.  The central factor cancels from every
conjugacy and commutator row but remains a free nontrivial Whitehead gauge.
All rows of the preceding cross-return table remain exact, and the marked
child is still

```text
C_1=e_(7_1,8_1) != 1.                                  (NDC9)
```

Hence adjoining one actual native depth-changing occurrence, its two-arm
return, and its complete middle-swap naturality only upgrades the finite
escape from `GL_6(F_2)` to `GL_7(F_2) times C_2`.  A live next relation
must compare one primed diamond arm with an independently returned source
arm without conjugating both sides by `J`; equivariant covariance leaves
the central `C_2` gauge untouched.

This is a scoped occurrence-table model, not a finite representation of the
full binary Leavitt Steinberg group.  No Property `(T)`, Kazhdan input,
stability theorem, trace hypothesis, literature theorem, or local
computation is used.

DERIVATION
first-native-diamond-cross-return-gl7-c2-proof
