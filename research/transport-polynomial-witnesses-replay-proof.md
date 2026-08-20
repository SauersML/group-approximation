---
rg: 2
id: transport-polynomial-witnesses-replay-proof
kind: route
title: Expand the transport polynomials and solve the Ledrappier recurrence
target: transport-polynomial-witnesses-replay
requires: []
artifacts:
  - experiments/renormalization_transport_audit.py
---

Expanding `(2I+S)^2` gives `(TPW1)` because the coefficients `4` vanish
modulo four.  For `(TPW2)`, after fixing `x_0`, the equations determine every
positive coordinate recursively and every negative coordinate recursively in
the other direction.  The two seed choices differ everywhere by one; setting
`y=0` proves that these are exactly the two kernel configurations.  The
script exhausts the finite-window recurrence and separately checks the
class-two Clifford square ledger used by the substitution audit.

