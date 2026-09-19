---
rg: 2
id: aggregate-morita-row-column-fold-has-d8-square-model
kind: claim
title: The aggregate Morita row-column fold has an exact D8-square marked model
artifacts:
  - research/aggregate-morita-row-column-d8-square-proof.md
distinct_from:
  degree-zero-leavitt-core-has-locally-finite-marked-models: that fences all balanced prefix coefficients but stops at gauge degree zero; this uses literal degree-one s_i and degree-minus-one t_i occurrences in one mixed aggregate commutator.
  aggregate-cross-commutator-sum-has-finite-s6-gauge: that forms completeness from the balanced cross coefficients p=s_0t_1 and r=s_1t_0; this forms it directly from the two Morita rows s_0,s_1 and t_0,t_1 and retains the marked q_1 output as one matching subcommutator.
  aggregate-binary-whitehead-does-not-read-completeness: that puts the same two Morita rows in one opposite-root Whitehead whose braid factorizes without using the range sum; this positive-root aggregate commutator really does use s_0t_0+s_1t_1=1 internally.
  leavitt-range-sum-fold-is-first-object-erasing-row: that compares three separately displayed long-root paths; this shares each child path as a literal factor of one aggregate row and one aggregate column before taking their commutator.
---

**ESTABLISHED FIRST NONZERO-DEGREE MIXED-CELL FENCE.**  On four stable
coordinates put

```text
S_0=x_79(s_0),        S_1=x_(7,10)(s_1),
T_0=x_98(t_0),        T_1=x_(10,8)(t_1),              (AMF1)
A=S_0S_1,             B=T_0T_1.
```

The factors of `A` share a row and the factors of `B` share a column, so
each pair commutes.  The two mismatched paths also commute.  The matching
commutators are

```text
C_i=[S_i,T_i]=x_78(s_it_i)=x_78(q_i),                 (AMF2)
```

and commute with every named factor.  Therefore

```text
[A,B]=C_0C_1=x_78(q_0+q_1)=x_78(1)=:N.               (AMF3)
```

Unlike a degree-zero cross-coefficient cell, `(AMF3)` contains the literal
uncancelled coefficients `s_0,s_1,t_0,t_1`.  Unlike the aggregate opposite
Whitehead, its derivation genuinely uses the Leavitt completeness row.  It
also types one displayed suboutput on the prescribed mark coefficient:
`C_1=x_78(q_1)` is a fixed root-position Weyl conjugate of
`z=x_13(q_1)`.

Nevertheless the complete displayed occurrence table has an exact finite
marked model.  Let

```text
D_8=<a,b,c | a^2=b^2=c^2=1, c=[a,b], [c,a]=[c,b]=1>
```

and work in `G=D_8 times D_8`.  Set

```text
S_0=(a,1),       T_0=(b,1),       C_0=(c,1),
S_1=(1,a),       T_1=(1,b),       C_1=(1,c),          (AMF4)
A=(a,a),         B=(b,b),         N=(c,c).
```

All row, column, crossed-path, matching-commutator, output-commutation, and
aggregate-completeness identities `(AMF1)--(AMF3)` hold exactly, while

```text
C_1!=(1,1).                                            (AMF5)
```

A fixed root-position occurrence transporting the named marked output may
be represented by identifying its target name with `C_1`; it adds no
relation between the two dihedral factors.  The left regular representation
of `G` is therefore an exact finite-dimensional unitary model in which the
marked output has a nonzero negative spectral projection.

Repeating this exact occurrence model at every tolerance and applying the
Atomic Leavitt Gap shows that this single aggregate coefficient-
completeness-to-mark cell cannot imply
`binary-leavitt-atomic-morita-return`.  The failure is precise: the mixed
word forms the parent output, but it leaves the two child commutator packets
as independent central directions `C_0,C_1`.  A useful continuation must
add an opposite-root or returned-payload occurrence which identifies those
directions on one prescribed marked reservoir; merely putting all four
Morita arms inside one aggregate positive-root commutator is insufficient.

This is a scoped occurrence-table model, not a finite representation of the
full binary Leavitt Steinberg group.  No Property `(T)`, Kazhdan input,
stability theorem, trace hypothesis, literature theorem, local computation,
or Lean compilation is used.

DERIVATION
aggregate-morita-row-column-d8-square-proof
