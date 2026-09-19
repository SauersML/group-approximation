---
rg: 2
id: binary-branch-flip-weyl-has-s3-c2-model
kind: claim
title: The literal binary branch-flip Weyl completion has an exact S3 by C2 marked model
invalidates:
  - branch-flip-weyl-closes-compression-fold-loop
artifacts:
  - research/binary-branch-flip-s3-c2-proof.md
distinct_from:
  closed-compression-fold-loop-retains-s3-gauge: that retains only the two compression-preimage edges and diagonal range-sum fold; this adjoins the actual opposite-root unit which swaps both branch coefficient arms.
  one-arm-range-sum-whitehead-has-marked-model: that fixes one arm in each branch and lets the complementary arms move independently; this tests the smallest EL20 word which swaps both fixed and complementary arms simultaneously.
  finite-extraspecial-mixed-words-cannot-ungauge-singer-transport: that stays inside a finite normal extraspecial extension; the coefficient unit here is the nonnormal full-Leavitt branch flip, and the surviving finite quotient is constructed directly.
---

**ESTABLISHED EXACT BRANCH-FLIP FENCE.**  In the binary Leavitt ring put

```text
u=s_0t_1+s_1t_0.                                      (BFW1)
```

The defining relations give

```text
u^2=1,
u s_0=s_1,       u s_1=s_0,
t_0u=t_1,        t_1u=t_0.                            (BFW2)
```

For spare indices `a!=b`, the ordinary opposite-root Weyl word

```text
F_ab=x_ab(u)x_ba(u)x_ab(u)                             (BFW3)
```

is the block matrix `[[0,u],[u,0]]`.  Hence, for an index `k` disjoint from
`a,b`,

```text
F_ab x_ak(s_i) F_ab^(-1)=x_bk(s_(1-i)),
F_ab x_ka(t_i) F_ab^(-1)=x_kb(t_(1-i)).                (BFW4)
```

After the fixed root-position relabeling already used by the two branch
charts, `(BFW4)` swaps the complete branch-`0` and branch-`1` coefficient
arms.  This is a genuine relation outside the character-only action tested
by the preceding closed-loop fence.  It has a fixed ordinary-relator
derivation: root additivity expands each `x(u)` into the two displayed
summands, and `(BFW2)--(BFW4)` use only the four binary inverse/cross-zero
relations and fixed Steinberg conjugation rows.

Nevertheless the entire compression/fold/branch-flip table has an exact
finite marked model.  Retain the three-character signs and transpositions

```text
J=diag(1,-1,-1),
C_0=diag(-1,-1,1),       C_1=diag(-1,1,-1),
W_0=(0 2),               W_1=(0 1)                    (BFW5)
```

on `C^3`, and the two Pauli factors from the one-arm model.  Let

```text
F=(1 2)_(C^3) tensor SWAP_(Pauli 0,Pauli 1).           (BFW6)
```

Then `F` fixes `J`, swaps `C_0,C_1`, swaps both full Pauli arm pairs, and

```text
F W_0 F^(-1)=W_1.                                     (BFW7)
```

Thus `(BFW4)` and every old compression-preimage, inverse, cross-zero,
transported-output, fixed-arm, and range-sum row are exact in the same
nonzero `J=-1` model.  The new full action is strictly larger than the old
character action: since `(1 2)=W_0W_1W_0` already lies in the character
`S_3`, adjoining `(BFW6)` also supplies the independent Pauli swap.  The
finite actor is therefore `S_3 x C_2`, and the marked projection still has
rank eight.

Consequently the first actual opposite-root relation coupling **both**
complementary branch arms enlarges the finite escape instead of collapsing
it.  It cannot establish `(ESB2)`.  The next candidate must distinguish the
two Pauli reservoirs after their literal branch exchange—for example by a
non-symmetric payload return—not merely swap the complete binary branches.
No Property `(T)`, Kazhdan input, trace profile, literature theorem, or
Steinberg lift is used.

## Attempts

- **Use the branch flip to identify the two complementary arms.**  It only
  exchanges them.  The Pauli tensor swap in `(BFW6)` implements that exchange
  exactly without identifying either factor with the other.
- **Combine the flip with the character hexagon.**  The character component
  cancels inside `S_3`, leaving the independent Pauli swap in the `C_2`
  factor; adding the flip twice kills both factors but also removes the
  proposed asymmetric branch move.

DERIVATION
binary-branch-flip-s3-c2-proof

