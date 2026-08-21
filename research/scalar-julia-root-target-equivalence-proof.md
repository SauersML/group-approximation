---
rg: 2
id: scalar-julia-root-target-equivalence-proof
kind: route
title: Replace the decoded additive commutator by its exact trace distance
target: scalar-trace-reflection-is-julia-root-target
requires:
  - one-additive-commutator-suffices-for-julia-return
  - fanizza-heat-filter-has-uniform-cstar-decay
---

The exact distance formula `(ACJ5)` gives `(SJR1)`.  Its bounded
self-adjoint refinement `(ACJ6)--(ACJ8)` attains that distance with one
unitary factor and the other of norm at most two.

Taking normalized trace in `(SJR4)` proves the forward implication to the
scalar mismatch.  Applying the bounded normal form to

```text
C-tr_d(C)I
```

proves the converse with residual `tr_d(C)I`, whose normalized-HS norm is
`|tr_d(C)|`.  This establishes the quantitative semantic equivalence.

Finally insert the NONHALT estimate
`tr(A_t)<=C_m/(4t^2)` into `(SJR2)`.  Once the selected root and presentation
defects vanish and `t` diverges, `(SJR3)` collapses the carrier trace.
