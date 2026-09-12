---
rg: 2
id: e5-tail-suppression-via-commuting-pulse-prefix
kind: route
title: Cut by earlier pulse signs and charge only prefix leakage
target: e5-tail-character-suppression-for-projected-exits
requires:
  - commuting-pulse-prefix-cuts-form-summable-first-hit-reservoir
  - packet-hard-transport-preserves-pulse-prefix
  - product-clock-synchronizes-fanizza-and-e5
---

Use the commuting pulse words themselves, rather than their top monomial
coefficients, to define the nested active carriers.  Equation `(PCF3)` leaves
only current hard-sign covariance and prefix leakage.  The product clock
supplies the former and `packet-hard-transport-preserves-pulse-prefix`
supplies the latter.
