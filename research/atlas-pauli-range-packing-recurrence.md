---
rg: 2
id: atlas-pauli-range-packing-recurrence
kind: claim
title: Pauli children recur through a finite projection range-packing automaton
distinct_from:
  atlas-pauli-branch-recurrence-automaton: that target is stated in branch-operator leakage and Gram norms; this target removes those analytic phases and asks only for the equivalent geometry of the word branches' final projections.
artifacts:
  - notes/TRUE_PAULI_BRANCH_TRANSFER_PACKET.md
---

Use the exact source `E` and children `R_0,R_1` from
`pauli-two-child-transfer-packet`.  Construct a fixed finite family of
canonical coefficient/multiplicity state projections `(P_i)` containing
`E,R_0,R_1`, together with fixed word-derived partial isometries `T_e` on a
strongly connected directed multigraph, such that every edge `e:i->j` has
source projection exactly `P_i` and, writing

```text
F_e = T_e T_e^*,
```

there is a dimension-independent `c>0` for which

```text
tau((1-P_j)F_e) = O(delta^c)                         (RPR1)
```

for every edge and

```text
sum_(e != f : target(e)=target(f)=j) tau(F_e F_f)
  = O(delta^c)                                       (RPR2)
```

for every target state `j`.  The exact edges `E->R_0` and `E->R_1` from the
Pauli packet must be included.

The state family and word menu are fixed independently of matrix dimension.
No spectral-radius estimate is requested: strong connectivity plus the
existing genuine two-child split at `E` supplies supercritical rational
pressure downstream.

## Why this is the right search object

For partial isometries, both costs in the previous formulation are purely
range-geometric:

- `partial-isometry-leakage-is-range-defect` turns `(RPR1)` into the required
  wrong-target branch leakage;
- `partial-isometry-gram-is-range-overlap` turns `(RPR2)` into the required
  ordered-pair Gram energy.

So phases of return words cannot repair a bad automaton.  The only viable
mechanism is to make their final range projections land almost inside the
right states and almost orthogonally to competing incoming ranges.

## Attempts

- **Reject merged returns immediately.** Any two positive-density returns onto
  the same final projection pay fixed cross-Gram mass by
  `common-range-isometries-have-maximal-gram-overlap`; the canonical inverse
  comb/raw returns already pay the explicit `1/4` ordered-pair floor recorded
  in `pauli-canonical-return-gram-floor`.
- **Search by range words.** For a candidate word `w`, first compute the final
  projection `w P_i w^*` (or its relator-controlled approximation) and only
  then ask whether a partial-isometry phase matters.  It does not affect the
  two capacity costs.
- **Mixed-relator priority.** Pure adjoints and raw inverse transport merge the
  children.  A viable recurrence must use mixed hard/comb or cross-root words
  whose range projections split again before entering a common target.