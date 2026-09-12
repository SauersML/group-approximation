---
rg: 2
id: aggregate-binary-whitehead-does-not-read-completeness
kind: claim
title: The aggregate two-branch Whitehead does not read completeness
artifacts:
  - research/aggregate-binary-whitehead-factorization-proof.md
distinct_from:
  native-opposite-arm-return-has-finite-s6-model: that authenticates one matching branch through a literal opposite root and gives a nontrivial finite permutation model; this tests the first apparent single-word coupling of both branches and proves that it factorizes before completeness is used.
  full-completeness-opposite-menu-has-finite-gl5-fusion: that contains both branches in fused payload copies and leaves the common-reservoir issue open; this isolates the natural three-factor aggregate Whitehead and shows it adds no cross-branch relation at all.
  leavitt-range-sum-fold-is-first-object-erasing-row: that identifies a long-root word which genuinely uses the range sum; this proves the tempting aggregate opposite-root word is not another such reader.
---

**ESTABLISHED EXACT FACTORIZATION FENCE.**  Use the active source coordinate
`1` and two target coordinates `6,7`.  Put

```text
X_0=x_16(s_0),          X_1=x_17(s_1),
Y_0=x_61(t_0),          Y_1=x_71(t_1),                 (ABW1)
R=X_0X_1,               L=Y_0Y_1.
```

These are the actual row and column occurrences of the binary Leavitt
module isomorphism on one three-coordinate payload corner.  It is tempting
to use

```text
P=RLR,
RLR=LRL                                                   (ABW2)
```

as one opposite-root relation reading both branches before their outputs
collapse to root labels.

It does not read completeness.  The root positions give

```text
[X_0,X_1]=[Y_0,Y_1]=[X_0,Y_1]=[X_1,Y_0]=1.             (ABW3)
```

Each matching inverse row `t_is_i=A` separately gives its ordinary partial
Whitehead braid

```text
X_iY_iX_i=Y_iX_iY_i.                                  (ABW4)
```

Using only `(ABW3)--(ABW4)`, one obtains

```text
RLR=(X_0Y_0X_0)(X_1Y_1X_1)
   =(Y_0X_0Y_0)(Y_1X_1Y_1)=LRL.                       (ABW5)
```

The coefficient row

```text
s_0t_0+s_1t_1=A                                       (ABW6)
```

does not occur anywhere in the derivation.  Thus `(ABW2)` is not a genuine
two-branch same-corner authentication despite its three-by-three block
appearance.

There is an exact finite model making the separation explicit.  In

```text
G=(S_3 times S_3) times (C_2 times C_2),               (ABW7)
```

let `X_i,Y_i` be the two adjacent transpositions in the `i`th `S_3` factor.
Let `C_0,C_1` be the two generators of the last Klein four factor and put
`J=C_0C_1`.  Then all branch, cross-commutation, aggregate Whitehead, and
fold-label rows are exact, while `J` is nonidentity.  The aggregate
opposite-root word places both branch factors in one group word but imposes
no relation between their partial-Whitehead packets and the independent
completeness fold.

Consequently the next candidate must include an occurrence in which the
**reverse products** `s_it_i` themselves enter the opposite-root
coefficient before being summed or compared.  Merely aggregating the
`s_i` row and `t_i` column is branchwise factorizable.  This claim is an
exact fence for `(ABW2)`, not a finite model after additionally identifying
the `C_i` fold labels with shared reverse-product payload paths.

No Property `(T)`, Kazhdan input, stability theorem, trace hypothesis, or
literature result is used.

DERIVATION
aggregate-binary-whitehead-factorization-proof

