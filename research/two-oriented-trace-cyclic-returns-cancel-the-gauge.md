---
rg: 2
id: two-oriented-trace-cyclic-returns-cancel-the-gauge
kind: claim
title: Two complementary trace-cyclic returns cancel an arbitrary stationary gauge layer
distinct_from:
  trace-cyclic-rank-mismatch-checksum: that compares one source with one prescribed smaller target; this permits an unknown multiplicity projection to choose the missing corner and cancels it by the opposite return orientation.
  partial-swap-row-orientation-cycle-needs-one-anchor: that shows pairwise comparisons leave one global relative-orientation bit and supplies a word anchor; this removes a whole operator-valued gauge projection at the scalar trace level without choosing an orientation.
  single-triangle-trace-cyclic-return-cell: that asks for one native group-word actuator producing the returned block maps; this supplies a strictly weaker two-orientation scalar endpoint for that actuator.
---

Let `E,H,G in M_d(C)` be projections with

```text
G<=H<=E.                                                   (TGR1)
```

Let `X_0,Y_0,X_1,Y_1` be arbitrary matrices.  Suppose

```text
|tr(Y_0 X_0)-tr(E)|
 +|tr(X_0 Y_0)-tr(E-H+G)| <= epsilon_0,                  (TGR2)

|tr(Y_1 X_1)-tr(E)|
 +|tr(X_1 Y_1)-tr(E-G)|   <= epsilon_1.                  (TGR3)
```

Then

```text
tr(H)<=epsilon_0+epsilon_1.                              (TGR4)
```

The projection `G` may depend arbitrarily on the matrix model.  It need not
be a packet word, have controlled rank, or be aligned between different
models.  Thus two return orientations eliminate an entire stationary
multiplicity gauge rather than merely a scalar sign.

For the native D8 carrier, `H` commutes with either Pauli reflection `R`, so

```text
G=H(1+R)/2,             H-G=H(1-R)/2                   (TGR5)
```

are the two complementary spin halves.  Their canonical packet traces are
both `1/16`, but `(TGR4)` does not use this balance.  A prospective native
cell may therefore return the two opposite D8 orientations without first
selecting which half is the correctly oriented chord carrier.

Equivalently, the hypothesis can be stated without naming `G`: it is enough
to decode target projections `F_0,F_1<=E` satisfying

```text
tr(F_0)+tr(F_1)=2tr(E)-tr(H)+o(1),                     (TGR6)
```

and one cyclic return from `E` to each `F_i`.  This is the weakest current
scalar endpoint for the proposed two-matching/nonflat triangle cell.

The theorem does not construct either return.  In particular, making
`(TGR2)--(TGR3)` universal tracial identities is forbidden by
`universal-block-return-violates-the-regular-firewall`.  Its gain is that a
matrix-only construction no longer has to synchronize or orient the hidden
chord gauge before paying the D8 mass.

