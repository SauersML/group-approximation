---
rg: 2
id: tagged-whitehead-two-branch-loop-has-a-three-qubit-marked-model
kind: claim
title: The first tagged Whitehead two-branch return loop has an exact three-qubit marked model
distinct_from:
  binary-leavitt-tagged-shift-table-has-centralizer-collisions: that constructs the exact private-column shift table and leaves its bounded-area coherence open; this tests the first mixed Whitehead completion of one tagged edge and shows that its local return data still do not encode Leavitt completeness.
  partial-whitehead-cell-has-marked-finite-model: that scalar-specializes one non-scalar Whitehead cell; this keeps two tagged branches, their crossed-zero commutators, and the adjacent Whitehead braid in a simultaneous nonscalar Pauli model.
  local-morita-sibling-cells-have-a-two-qubit-periodic-absorber: that alternates two untagged Pauli factors through an arbitrary local tree; this includes a private commuting tag and computes the literal mixed return loop through the actual swap implementers.
artifacts:
  - research/tagged-whitehead-two-branch-loop-countermodel-proof.md
---

**ESTABLISHED SCOPED NO-GO.**  Consider the first bounded prototype obtained
by completing a private-column tagged edge with a literal Whitehead
transport.  Abstract its two branch rows, tagged columns, common mark and
two adjacent Whiteheads as

```text
C_r,H_r,K,J,W_12,W_23,                    r=1,2,3,
```

and retain the following exact rows:

```text
J^2=C_r^2=H_r^2=K^2=W_12^2=W_23^2=1,
[C_r,H_r]=J,              [C_s,H_r]=1       (s!=r),    (TWL1)
[K,C_r]=[K,H_r]=1                         (r=1,2),
[K,W_12]=1,
W_12(C_1,H_1)W_12^(-1)=(C_2,H_2),
W_23(C_2,H_2)W_23^(-1)=(C_3,H_3),                       (TWL2)
W_12W_23W_12=W_23W_12W_23.                             (TWL3)
```

Here replacing `H_r` by the tagged column `H_rK` preserves its diagonal
marked commutator and every crossed-zero commutator.  The natural mixed
two-branch return prototype is the literal null loop

```text
L_12^K=W_12[C_1,H_1K]W_12^(-1)[C_2,H_2K]^(-1)=1.       (TWL4)
```

The loop `L_12^K` uses an opposite-root Whitehead word, both branches, the
private tag, and the packet payload in one fixed cell; the adjacent untagged
loop `L_23` is retained to test the braid completion.

Nevertheless `(TWL1)--(TWL4)` have an exact eight-dimensional unitary model
with `J=-I`.  Thus this concrete mixed-loop completion cannot be the
load-bearing prototype in
`binary-leavitt-three-row-atomic-compiler`.  If all prototype discrepancies
used by a proposed compiler are consequences of this table, they vanish in
the marked model, whereas `(BAC1)` would demand an exact binary Leavitt
family in its nonzero `J=-1` corner, contradicting the Atomic Leavitt Gap.

The obstruction is exact and narrowly scoped.  It does not rule out a
mixed/opposite-root prototype which remembers the **coefficient
range-sum/parent-generation occurrence** rather than merely transporting
the same marked commutator between two Pauli factors.  In particular, the
next candidate must fail the three-qubit factor-reuse model by making the
two branch ranges add to the named parent on the selected atom.  Neither a
private commuting tag nor the adjacent Whitehead braid supplies that row.

No Property `(T)`, Kazhdan input, stability theorem, or literature result is
used.

DERIVATION
tagged-whitehead-two-branch-loop-countermodel-proof
