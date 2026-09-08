---
rg: 2
id: laurent-elementary-groups-are-residually-finite
kind: claim
title: Elementary groups over integral and binary Laurent polynomial rings are residually finite
distinct_from:
  binary-jacobson-mf-radical-dichotomy: that computes the two-valued MF radical of the binary Jacobson elementary group and uses residual finiteness of its symbol quotient as one input; this isolates that input, proves it over the integers as well, and mentions no Jacobson ring.
  binary-jacobson-elementary-mark-is-finite-quotient-invisible: that is a negative statement about finite quotients of the Jacobson elementary group; this is a positive separation statement about the Laurent quotient group.
artifacts:
  - research/artifacts/fullness-corner-and-order-two-reduction-2026-09-08.md
---

**ESTABLISHED.**  For every `n >= 2` and for `C = F_2` or `C = Z`, the
group `EL_n(C[z,z^(-1)])` is residually finite, hence MF.

The separating quotients are entrywise specializations
`z |-> ` a nonzero element of a finite field, giving finite general
linear groups.

Both cases are used downstream: the binary one is the symbol quotient of
the binary Jacobson elementary group, the integral one is the symbol
quotient of the universal order-two ring `A_2` in
`order-two-universal-ring-has-finitary-symbol-sequence`.

DERIVATION
laurent-elementary-residual-finiteness-proof
