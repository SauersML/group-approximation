---
rg: 2
id: marked-star-outer-corrected-whiteheads-are-quarter-swaps
kind: claim
title: Outer-correcting the prefix Whiteheads swaps the three marked-star cells but retains two quarter labels
artifacts:
  - research/marked-star-outer-corrected-whitehead-proof.md
distinct_from:
  marked-root-star-carries-three-anchored-cells: that supplies the positive distinct-center carrier and the three Pauli cells but leaves their native prefix products unauthenticated; this computes the strongest literal adjacent-cell transports preserving that carrier.
  same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps: that uses three cells with one common center; this combines the same prefix Whiteheads with constant outer Weyls so that they swap the three distinct centers of the marked-root star.
  same-center-whitehead-gram-is-not-native-selector-gram: that fences the equal-label construction on the common-center carrier; this proves the analogous equal-label boundary directly on the positive marked-star carrier.
  same-center-m8-commutators-cannot-wordize-one-eighth-reflection: that uses determinant one for an arbitrary two-word commutator; this shows that every word in the entire outer-corrected marked-star actor packet has determinant one on its eight-dimensional label representation.
  binary-leavitt-two-shared-gauge-selector-compiler: that requires target label fractions one quarter and one eighth together with source fractions one half and one quarter; this obtains conjugate gauges for two one-quarter adjacent swaps only.
---

Retain the positive carrier and anchored cells of
`marked-root-star-carries-three-anchored-cells`.  Thus

```text
E=P_z P_(x_42(q),-) P_(x_52(q),-) P_(x_62(q),-),
tau(E)>=(11/1360)tau(P_z),                             (MSW1)
```

and on `EH` the pairs

```text
(A_1,B_1)=(x_47(a_1),x_72(b_1)),
(A_2,B_2)=(x_58(a_2),x_82(b_2)),
(A_3,B_3)=(x_69(a_3),x_92(b_3))                       (MSW2)
```

are three cross-commuting Pauli pairs.  Let `J_1,J_2` be the literal
prefix Whiteheads on the middle coordinates `(7,8)` and `(8,9)`, and let

```text
L_1=w_45(1),                 L_2=w_56(1),
U_1=L_1J_1,                 U_2=L_2J_2.               (MSW3)
```

The constant outer Weyls commute with both prefix Whiteheads.  The two
fixed words preserve `E` and act on `(MSW2)` by the adjacent
transpositions

```text
Ad(U_1):(A_1,B_1)<->(A_2,B_2),
Ad(U_2):(A_2,B_2)<->(A_3,B_3),                        (MSW4)
```

fixing the remaining pair.  They are involutions and satisfy the Coxeter
braid

```text
U_1U_2U_1=U_2U_1U_2.                                  (MSW5)
```

Consequently, after writing

```text
EH=(C^2)^(tensor 3) tensor M,
```

there are reservoir involutions `V_1,V_2` with

```text
U_1|_E=SWAP_(1,2) tensor V_1,
U_2|_E=SWAP_(2,3) tensor V_2.                         (MSW6)
```

The braid makes `V_1,V_2` unitarily conjugate.  This is a literal
same-reservoir transport theorem on the positive marked-star carrier, valid
for every finite-dimensional trace profile after exactification of the
fixed packet.

It is not the unequal selector compiler.  Both fixed label swaps in
`(MSW6)` have negative rank `2` in dimension `8`, hence label fraction
`1/4`.  In fact the whole marked-star actor packet has an exact determinant
fence.  Every Pauli generator has four negative eigenvalues, and each
adjacent swap has two.  Hence the label image of

```text
<A_1,B_1,A_2,B_2,A_3,B_3,U_1,U_2>
```

lies in `SU(8)`.  Any involution in this label image has even negative
multiplicity.  The one-eighth reflection has negative multiplicity one and
determinant `-1`, so it is not the label action of **any** word in this
packet, not merely absent from the displayed generators.

Moreover the literal chained A-side Hecke words are transparent to the
star cut:

```text
[E,A_1]=[E,A_2]=1,
supp|EA_1E|=supp|EA_2A_1E|=E.                         (MSW7)
```

Thus the marked-star compression gives target support fractions `1,1`, not
`1/4,1/8`.  The uncorrected `J_i` also commute with `E`, so their
compressions are full unitaries; before the outer correction they send the
first arm to a forked arm with the old outer index, rather than to the next
cell:

```text
J_1 A_1 J_1^(-1)=x_48(a_2),
J_1 B_1 J_1^(-1)=B_2,                                 (MSW8)
```

and similarly at the next scale.  Equation `(MSW3)` repairs exactly this
outer-index mismatch, but it cannot change the two equal quarter label
ranks.

Therefore the positive marked-star carrier supplies actual conjugate
transport gauges and mixed Pauli covariance only for the equal
quarter/quarter adjacent-swap pair.  It cannot be directly substituted for
the native rows with source/target fractions

```text
(1/2,1/4),                 (1/4,1/8).                 (MSW9)
```

A continuation still needs a representation-dependent odd occurrence
which attaches a one-eighth controlled label, or two authenticated unequal
source-to-quarter rows.  The common star carrier and outer correction do
not supply either attachment.  No Property `(T)`, Kazhdan input, canonical
trace substitution, or literature theorem is used.

DERIVATION
marked-star-outer-corrected-whitehead-proof
