---
rg: 2
id: central-sign-assignment-atom-is-index-two-reynolds-surplus
kind: claim
title: A central-sign assignment atom is exactly one index-two Reynolds surplus
distinct_from:
  central-sign-bcs-atoms-are-subgroup-reynolds-projections: that writes the negative-sector assignment atom as one subgroup average times the central cut; this identifies it as the orthogonal difference of two nested subgroup averages and fixes the HNN orientation.
  subgroup-hecke-hnn-is-a-regular-safe-rank-actuator: that gives the general one-sided HNN estimate for arbitrary finite subgroups; this supplies a canonical index-two pair whose surplus is precisely the forbidden atom.
  central-sign-reynolds-first-hit-compiler: that must make successive exits summable while retaining active mass; this solves only the local active/exit split at one level.
---

Let

```text
C=<x_1,...,x_k,J>~=C_2^(k+1),
H_a=<x_i J^(a_i):1<=i<=k>,
Q_-=(1-J)/2.
```

Then `H_a` has index two in `C`, `C=<H_a,J>`, and their Reynolds
projections satisfy the group-algebra identity

```text
e_(H_a)-e_C=e_(H_a)Q_-.                               (ISR1)
```

By `central-sign-bcs-atoms-are-subgroup-reynolds-projections`, the right
side is exactly the assignment atom `A_a` on the negative central sector.
Thus in every unitary representation

```text
Fix(H_a)=Fix(C) orthogonal_sum Ran(A_a),                (ISR2)
tr(e_(H_a))-tr(e_C)=tr(A_a).                           (ISR3)
```

There is consequently no local orientation problem for this central-sign
front end.  Apply `subgroup-hecke-hnn-is-a-regular-safe-rank-actuator` with
`K=H_a`, `H=C`, and the inclusion `H_a->C`.  If `u` is its stable letter,
then

```text
u e_C u^*<=e_(H_a),
R_a=e_(H_a)-u e_C u^*                                 (ISR4)
```

is an exit projection with

```text
tr(R_a)=tr(A_a).                                       (ISR5)
```

The approximate HNN relations pay the failure of the inclusion with the
dimension-independent estimate `(SHA5)`.

This does not by itself solve the first-hit compiler.  In the canonical
regular trace `(ISR5)` is positive, so repeating the same split cannot make
arbitrarily many exact orthogonal exits while keeping the active carrier
stationary.  What remains is the matrix-only persistence and successive
layer placement required by `branching-plus-first-hit-exits-forces-hs-floor`,
not predicate naming or one-edge rank orientation.

