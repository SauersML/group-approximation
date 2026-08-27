---
rg: 2
id: direct-fano-uncovered-row-commutator-proof
kind: route
title: Insert the uncovered projection into the existing free-Julia row inequality
target: uncovered-ghost-reflections-directly-pay-the-fano-row
requires:
  - free-julia-grading-carries-one-gram-at-canonical-quarter-mass
  - finite-packet-central-sign-cannot-enforce-nonlinear-support
  - ghost-finite-router-induced-sector-or-perfect-corner
  - centralizing-d8-word-anchors-relative-row-orientation
---

For `r_c`, the diagonal blocks in `(FJG4)` are

```text
A_c=P_+-2Q_c,                 B_c=P_-.                  (DFU1)
```

Since `P_+S=S=SP_-`, one has `A_cS-SB_c=-2Q_cS`.
Substitution into `(FJG4)` gives `(UGR3)`. Equal grading ranks convert the
whole-space trace of `S^*Q_cS` to one half of its one-block normalized trace,
giving `(UGR4)`; weighting and summing gives `(UGR5)`.

For completeness, the partial-swap reflection has positive diagonal block
`1-SS^*`. From `Q_cS=0` one gets `Q_cSS^*=SS^*Q_c=0`, so `r_c` commutes
with that diagonal block and with `S`, hence with the whole reflection `j`.

Finally the uncovered sign table is nonaffine, so central words cannot
express it. A finite router can hard-code it only in a chosen type; induction
of the uncovered selector character produces the exact countersector from
`ghost-finite-router-induced-sector-or-perfect-corner`.
