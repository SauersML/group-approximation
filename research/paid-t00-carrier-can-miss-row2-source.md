---
rg: 2
id: paid-t00-carrier-can-miss-row2-source
kind: claim
title: The paid t00 carrier can miss the actual row-two signed Hecke source
artifacts:
  - research/paid-t00-row2-source-incidence-proof.md
  - experiments/marked_t00_signed_source_incidence_audit.py
distinct_from:
  native-t00-y1-collision-pays-marked-opnorm: that proves the discrepancy root has a positive common carrier with the mark and maximal T/Y mismatch there; this adjoins the literal center-chain source projection and shows that the currently typed row-two action table need not put any of that carrier in the source.
  marked-t00-separation-has-gl10-model: that keeps the globally paid discrepancy transverse to every unnamed source corner; this names the actual signed source `e_chi z_<x_94(b_3),x_92(b_3)>` and gives a reducible finite model where both it and the paid carrier are nonzero but orthogonal.
  middle-index-order-seven-orbit-cut-is-native-scale-neutral: that produces a fixed marked Fano atom orthogonal to the signed Hecke character; this retains the paid t00 discrepancy and its explicit double-commutator return to the mark.
---

Let

```text
D=x_78(t_00+s_0t_00),          P_pay=P_zP_D
```

be the paid discrepancy carrier, and let the actual row-two signed source be

```text
r_2=e_chi z_U,
H=<x_65(q),x_54(q),x_42(q)> ~=UT_4(F_2),
U=<x_94(b_3),x_92(b_3)> ~=F_2^2.                      (PRS1)
```

The root rectangles show that `D` commutes with `H` and `U`, and the marked
root `z=x_13(q)` does as well.  Hence `P_pay` and `r_2` commute.  The
currently authenticated row-two occurrence table nevertheless gives no
positive lower bound for their intersection:

```text
rank(P_pay r_2)=0                                     (PRS2)
```

is compatible with a finite exact model in which both projections are
nonzero, the mark and discrepancy survive, and the row-two `A_2` occurrence
is globally nontrivial.

The model is a direct sum of two exact blocks.

1. Extend the transverse `GL_10(F_2)` occurrence model by two vertices so
   that the literal center chain and source roots are

   ```text
   h_3=e_(u,10),       h_2=e_(10,r),       h_1=e_(r,s),
   f=[B_3,h_2]=e_(9,r),
   k=[B_3,[h_2,h_1]]=e_(9,s).                         (PRS3)
   ```

   This block retains the adjacent braid, both order-seven heads, the
   marked-center action, both parallel `A_2` paths, `T!=Y`, and the marked
   double-commutator saturation.  In its permutation representation on
   `F_2^12`, exact fixed-space summation gives

   ```text
   tr(r_2)=0.                                         (PRS4)
   ```

   The literal `A_2` transvection is nonidentity on this block.

2. On an eight-dimensional three-qubit block put

   ```text
   D=Z_1,               z=Z_3,               h=Dz=Z_1Z_3.
   ```

   Map all three simple generators of `H` to `h` and both generators of
   `U` to `1`.  Then `r_2=(1-h)/2` has rank four, while `P_pay` has rank two
   and

   ```text
   P_pay r_2=0                                           (PRS5)
   ```

   because `D=z=-1` forces `h=Dz=+1`.  This is not an
   untyped sign table: with CNOT actors one has exactly

   ```text
   [[CNOT_(2->1),D],CNOT_(3->2)]=z,                  (PRS6)
   CNOT_(1->3) z CNOT_(1->3)=h,                     (PRS7)
   [CNOT_(1->2)CNOT_(3->2),Z_2]=h.                  (PRS8)
   ```

   Thus the paid normal return, the marked-center Weyl transport, and the
   marked-center commutator cell all remain nontrivial.  On this summand the
   row-two `A_2` and its parallel paths collapse, while `J_2=B_3=Z_2`
   makes `(J_2B_3A_2)^7=1` and the native braid exact.

Their direct sum has nonzero `r_2`, nonzero `P_pay`, zero intersection, and
nontrivial `A_2` supplied by the first block.  This reducibility is an escape
inside an arbitrary representation profile: the presently named relations
do not force this fixed signed source and the paid discrepancy to occur in
the same representation summand.

The quantifier boundary is important.  Here `r_2` is the literal signed
Hecke projector `e_chi z_U` from `(PRS1)`, with the fixed nontrivial character
`chi` of the three simple center-chain roots.  The model therefore fences a
dimension-free incidence claim for that authenticated row-two source.  It
does **not** classify every source projection allowed by the
arbitrary-profile selector dichotomy, and in particular does not prove that
every profile-dependent choice of `Q` misses `P_pay`.

This is a scoped finite model of the displayed row-two occurrence and
source table, not a representation of the full binary-Leavitt Steinberg
group.  In particular the second summand kills `A_2`; a successful
full-presentation continuation must add a fixed normal-saturation or
incidence row which prevents that segregation and charges its leakage on
the paid carrier.  `J_2`, its order-seven head, the one marked-center return,
and the two parallel `A_2` factorizations do not provide such a row.

No Property `(T)`, Kazhdan input, canonical trace, literature theorem,
local computation, or Lean compilation is used.

DERIVATION
paid-t00-row2-source-incidence-proof
