---
rg: 2
id: branch-flip-weyl-joins-complementary-q-child-to-native-head
kind: claim
title: The branch-flip Weyl joins the complementary q child to the native head but retains an SL13 fence
artifacts:
  - research/branch-flip-q-child-sl13-fence-proof.md
distinct_from:
  one-arm-return-of-complementary-q-child-stays-orthogonal: that proves the separate a1 and b1 returns close an orthogonal SL3 packet; this adjoins their sum as the involutive coefficient of one opposite-root Weyl word and obtains a literal conjugacy from the q-child root to a native p-root.
  binary-branch-flip-weyl-has-s3-c2-model: that applies the branch flip to the compression/fold character and Pauli table; this applies the same coefficient unit on the two repeated coordinates of the complementary q-child packet and computes the resulting common elementary carrier.
  binary-leavitt-two-label-difference-occurrence-cells: that asks for two label-only odd comparisons with the actual native selector rows on a positive analytic subcorner; this supplies one exact child-to-native root conjugacy but proves that its complete finite packet still has zero full-Hecke source.
---

**ESTABLISHED COMMON-CARRIER OCCURRENCE AND FINITE FENCE.**  In the binary
Leavitt algebra put

```text
p=s_0t_0,             q=s_1t_1,
a_1=s_1t_0,           b_1=s_0t_1,           w=a_1+b_1. (BFQ1)
```

Continue the complementary-child notation

```text
Q=x_(7,10)(q),        U=x_(10,2)(a_1),
V=x_(2,7)(b_1),                                      (BFQ2)
```

whose elementary image is the `SL_3(F_2)` packet on

```text
C={p@2,q@7,q@10}.
```

The coefficient `w` is an involution exchanging the two first-level
cylinders.  Form the ordinary Steinberg Weyl word

```text
Omega=x_(7,10)(w)x_(10,7)(w)x_(7,10)(w).             (BFQ3)
```

Then ordinary Steinberg conjugation, using one spare index for the first
opposite-root output, gives the literal occurrences

```text
Omega Q Omega^(-1)=x_(10,7)(p),
Omega U Omega^(-1)=x_(7,2)(p),
Omega V Omega^(-1)=x_(2,10)(p).                      (BFQ4)
```

The first output in `(BFQ4)` is an opposite root in the existing native
`SL_10(F_2)` head, since that head uses `p@7,p@10`.  Thus the branch flip
does exactly what the separate one-arm returns do not: it puts the
complementary `q` root and a native root in one literal conjugacy
occurrence.  The other two outputs are the two orientations connecting
`p@2` to that native `p` pair.

This common carrier still has an exact finite fence.  The ten native atoms

```text
H={q@1,q@2,q@3,q@4,q@5,q@6,p@7,e_2@8,e_3@9,p@10}
```

together with `C` are thirteen pairwise orthogonal Leavitt matrix-unit
atoms.  On them, `Omega` is the permutation

```text
(p@7 q@10)(p@10 q@7).                                 (BFQ5)
```

The old factors are `SL(H)` and `SL(C)`.  Conjugating `SL(H)` by `(BFQ5)`
and taking elementary commutators first generates `SL(H union {q@7,q@10})`;
adjoining `SL(C)` then generates the entire

```text
SL_13(F_2)                                             (BFQ6)
```

on the thirteen atoms.  Thus this is not a residual direct-product gauge:
the two packets really do share one finite elementary carrier.

Let `pi_13` be the permutation representation of `(BFQ6)` on the `8191`
nonzero vectors of `F_2^13`.  It is an exact finite model of the
completeness table, both one-arm returns, `Omega`, the marked-star packet,
and the adjacent native Whiteheads.  For the marked root `z`, the
three-root star projection `E`, and the literal full-Hecke signed source
`F_Hecke`, it has

```text
rank pi_13(P_z)=2048,       rank pi_13(E)=512,
rank pi_13(F_Hecke)=0.                                  (BFQ7)
```

The last equality is the same negative-stabilizer certificate as in the
native projective head: it applies to every thirteen-bit vector because
the three inspected chain coordinates are unchanged and the other bits are
spectators.

Consequently the branch-flip Weyl word supplies a proved common-carrier
occurrence, but not either label-only odd comparison required by
`binary-leavitt-two-label-difference-occurrence-cells`.  A native/child
conjugacy alone can enlarge the finite escape from `SL_10 times SL_3` to
`SL_13` while the marked and star projections stay nonzero and the
full-Hecke source stays zero.  Any successful successor must add a row not
realized in this thirteen-atom matrix-unit packet, or authenticate one of
the two selector signs on a positive source cut rather than merely join the
root carriers.

This is an elementary-image finite packet fence, not a representation of
the full infinite Steinberg group.  No Property `(T)`, canonical trace,
literature theorem, or computation is used.

DERIVATION
branch-flip-q-child-sl13-fence-proof
