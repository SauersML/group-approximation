---
rg: 2
id: branch-reset-amalgam-preserves-mark-and-balances-types
kind: claim
title: Amalgamating the branch reset preserves the marked base and balances selector types
distinct_from:
  branch-controlled-pauli-selector-reset: that constructs and analyzes the finite reset group; this attaches it to an arbitrary marked packet group and gives the approximate multiplicity consequence.
  finite-graph-of-groups-representation-types-are-integer-flows: that shows a whole finite graph of finite groups cannot create global curvature; this uses one finite edge only as a loss-controlled center reset inside an infinite Toeplitz recurrence.
---

Let `G` contain the child selector subgroup

```text
D=<J,q,z_1,...,z_k>
```

and a nonidentity marked word `w`. Let `R` be the finite branch-reset group of
`branch-controlled-pauli-selector-reset`, containing the same `D`, and form

```text
Gamma=G *_D R.                                                (BRA1)
```

Then:

1. the canonical map `G->Gamma` is injective, so `w` remains nonidentity and
   the left regular representation of `Gamma` is an exact marked model;
2. in every finite-dimensional exact `J=-1` representation of `R`, the
   multiplicities of all `z`-characters are equal inside each fixed
   `q`-branch; and
3. for an approximate matrix representation of `(BRA1)`, independently
   exactifying the fixed child packet and `R` and aligning their common `D`
   actions bounds the normalized weighted `L1` failure of this balance by
   `C sqrt(E)`, for a constant depending only on the fixed reset table.

Thus selector-center reset has both exact marked completeness and a
dimension-free type-vector payment. It does not yet identify the reset
selector chart with the next Fanizza context; that is the remaining
context-atlas interface in `toeplitz-schur-child-masa-recurrence`.
