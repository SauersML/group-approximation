---
rg: 2
id: one-arm-range-sum-whitehead-has-marked-model
kind: claim
title: One individual arm per range-sum Whitehead still has a marked three-character model
distinct_from:
  payload-range-sum-whitehead-has-three-character-model: that authenticates the inverse and reverse output commutators but permits both individual arms to change under each Whitehead; this fixes one full individual Pauli arm through each Whitehead, including on the prescribed marked atom.
  literal-whiteheads-give-gauged-moving-bridge-table: that supplies exact full-Gram subgroup-moving bridges but retains their reservoir gauge; this shows at the atomic coefficient level that one fixed arm can be gauge-free while all carrier motion remains in the complementary arm.
  binary-leavitt-three-row-atomic-compiler: that needs both inverse maps and completeness inside one prescribed atom; this proves that one individually authenticated arm per branch still does not return the complementary coefficient carrier to that atom.
artifacts:
  - research/one-arm-range-sum-three-character-proof.md
---

**ESTABLISHED EXACT ONE-ARM COUNTERMODEL.**  Strengthen the minimal
payload-coupled range-sum table `(PCR1)--(PCR2)` by requiring that, after
the fixed spare-index role rotation, each Whitehead fixes one complete
individual coefficient arm:

```text
W_iX_iW_i^(-1)=X_i,                         i=0,1.      (OAR1)
```

The same named arm is therefore used in both the inverse and reverse
product occurrences:

```text
[X_i,Z_i]=J,
[X_i,W_iZ_iW_i^(-1)]=C_i,
C_0C_1=J,                                  [X_i,Z_j]=1 (i!=j).  (OAR2)
```

This is the strongest equality-level authentication of one arm: it is an
ordinary full-space identity, not merely equality after compression to the
`J=-1` atom.  It models the actual partial-Whitehead coefficient table after
one root-position relabeling: the shared outer coefficient occurrence is
named once, while the complementary `t_i`/`s_i` arm is transported from the
inverse output `A` to the reverse output `s_it_i`.

Even `(OAR1)--(OAR2)` have an exact twelve-dimensional unitary model with a
nonzero `J=-1` atom.  The authenticated arms can act globally on two Pauli
factors and hence commute with the Whiteheads.  The complementary arms are
controlled by the three different negative character supports and absorb
all Whitehead motion.  Thus adding one individual arm per branch kills no
part of the three-character escape.

Consequently this prototype does not imply `(BAC1)`.  The next genuine seam
must also authenticate the **complementary arm**, or insert a mixed cross-arm
row which forces its `C_i=-1` support back inside the prescribed `J=-1`
atom.  If both transported arms returned to the same named `J`-Pauli pair,
their commutator would give `C_i=J`; then `C_0C_1=J` would kill `J`.
The exact model proves that no conclusion of that strength follows from
only one arm.

No Property `(T)`, Kazhdan input, stability theorem, or literature result is
used.

DERIVATION
one-arm-range-sum-three-character-proof
