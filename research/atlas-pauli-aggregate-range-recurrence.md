---
rg: 2
id: atlas-pauli-aggregate-range-recurrence
kind: claim
title: Pauli recurrence is witnessed by almost-projection aggregate incoming ranges
distinct_from:
  atlas-pauli-range-packing-recurrence: that target asks separately for every wrong-target range cost and every pairwise incoming overlap; this target packages all incoming branches at a state into one positive aggregate range operator.
artifacts:
  - notes/TRUE_PAULI_BRANCH_TRANSFER_PACKET.md
---

Use the exact source `E` and children `R_0,R_1` from
`pauli-two-child-transfer-packet`.  Construct a fixed finite family of
canonical coefficient/multiplicity projections `(P_i)` containing
`E,R_0,R_1`, together with fixed word-derived partial isometries `T_e` on a
strongly connected directed multigraph.  Every edge `e:i->j` has source
projection exactly `P_i`, and the two exact Pauli edges `E->R_0,E->R_1` are
retained.

For each target state `j`, form the single positive aggregate incoming range
operator

```text
F_j = sum_(e: target(e)=j) T_e T_e^*.
```

There is a dimension-independent `c>0` such that in every sufficiently
accurate trace-preserving atlas microstate,

```text
tau((1-P_j)F_j) = O(delta^c),                           (ARR1)
||F_j^2-F_j||_2 = O(delta^c)                            (ARR2)
```

for every target `j`.

The state family and word menu are fixed independently of matrix dimension.
No pairwise Gram estimates and no spectral-radius computation are requested.

## Why this is a smaller compiler target

`ARR1` is one total range-containment estimate per state.  Because its summands
are nonnegative in trace, it controls every individual incoming leakage.
`ARR2` says that the **sum** of incoming final projections is almost a
projection.  By `aggregate-range-idempotence-replaces-gram-bookkeeping`, this
one defect controls the sum of all ordered pairwise Gram overlaps.

So a recurrence search can work at the level of named aggregate carriers:
identify a word identity or relator-controlled approximation saying that all
incoming ranges at one automaton state nearly partition one projection.  This
matches the algebra already visible in the exact Pauli split, where the two
child ranges satisfy exactly

```text
T_0T_0^* + T_1T_1^* = U^* Q U.
```

The new work is to arrange analogous aggregate range identities on the return
part of a strongly connected finite automaton.  It is potentially much easier
than proving quadratic many pairwise orthogonality estimates.

## Attempts

- **Search for Cuntz-style sums, not zero products.** A word calculation which
  identifies `sum_e T_eT_e^*` with one named coefficient projection gives
  `ARR2` for free, even when no individual cross term has a simple normal form.
- **Allow approximate partitions.** Exact equality is unnecessary.  A fixed
  relator certificate controlling the aggregate idempotence defect at a power
  of `delta` is enough.
- **Reject common-range inverse returns.** Their aggregate is `2E`, whose
  idempotence defect is order one; the existing canonical-return Gram no-go is
  recovered immediately without examining either cross term.
