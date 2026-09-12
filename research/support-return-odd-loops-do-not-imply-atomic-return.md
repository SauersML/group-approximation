---
rg: 2
id: support-return-odd-loops-do-not-imply-atomic-return
kind: claim
title: The authenticated support-return odd loops do not imply an atomic Leavitt return
distinct_from:
  support-return-selector-occurrence-fence: that classifies the missing quarter/eighth selector typing; this removes selector ranks entirely and tests the weaker three-row Atomic Morita Return and the operator-norm coarse/fine leakage row.
  binary-leavitt-atomic-morita-return: that is the global open decoder target for the full finite presentation; this is a finite-fragment fence saying that the authenticated support-return menu by itself cannot establish that target.
  opnorm-leavitt-coarse-fine-return-row: that asks the full presentation to derive a common coarse/fine carrier; this shows that the support-return identities, chart covariances and native braid do not derive it.
---

**ESTABLISHED FINITE-FRAGMENT FENCE.**  Let `T_SRL` be the compressed
finite occurrence table on the recentered marked carrier consisting of

```text
J_i=W_i(Z_iH_iZ_i)W_i,                                (SRA1)
```

the Pauli-chart covariance rows in `(SRL7)--(SRL8)`, the exact chart
intersection rows `(SCI1)--(SCI6)`, and the native Coxeter braid for
`J_1,J_2`.  The table has an exact finite-dimensional unitary model on a
nonzero marked atom.  In that model the extraspecial center, hence the
compressed marked involution, acts as `-I`; the two chart transporters retain
independent central `C_2` signs.

Consequently `T_SRL` alone implies neither of the following outputs on the
prescribed marked atom:

1. four bounded operators satisfying the two diagonal inverse rows and the
   completeness row of `binary-leavitt-atomic-morita-return` with a modulus
   tending to zero;
2. exact depth-one and depth-two matrix-unit packets with one nonzero common
   identity and a coarse-to-fine support leakage tending to zero, as in
   `opnorm-leavitt-coarse-fine-return-row`.

Indeed, use the same exact marked model at every tolerance `t>0`.  Its table
defect is zero and its rounded marked projection is the identity.  Output 1
would give, for arbitrarily small `t`, operators in a fixed nonzero finite
matrix corner whose three binary Leavitt defects are at most `eta(t)`.
`atomic-leavitt-gap-on-nonzero-matrix-corner` instead gives

```text
1 <= ||t_0s_0-p||_op+||t_1s_1-p||_op
     +||s_0t_0+s_1t_1-p||_op,                         (SRA2)
```

contradicting `eta(t)->0`.  Output 2 would give a unitary return from a
coarse minimal corner of rank `rank(P)/2` to a fine one of rank
`rank(P)/4` with leakage `omega(t)->0`.  But
`rank-deficient-return-row-has-operator-norm-one` makes that leakage exactly
one for every unitary, again a contradiction.

This is a scope fence, not a refutation of either global open target.  A
successful atomic decoder must use at least one additional ordinary-word
relation outside `T_SRL` which couples coefficient completeness to the
prescribed marked atom.  Recombining the two odd identities, their braid,
or their common two-pair chart cannot do so: all of those rows remain exact
in the marked finite gauge model.

No Property T, Kazhdan input, trace hypothesis, literature theorem, local
computation or Lean compilation is used.

DERIVATION
support-return-atomic-return-fence-proof
