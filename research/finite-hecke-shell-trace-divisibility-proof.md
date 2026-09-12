---
rg: 2
id: finite-hecke-shell-trace-divisibility-proof
kind: route
title: Apply the order-twenty-four bound before testing support or covariance
target: no-finite-arithmetic-hecke-corner-can-have-shell-atom-trace
requires:
  - sl3-one-over-forty-two-packet-is-external-or-folded
  - native-c2-hecke-corner-cannot-wordize-the-a2-average
---

The canonical trace on `C[K]` is the normalized matrix trace in the left
regular representation, proving `(FHC2)`.  A nonzero projection has positive
integer rank.  The imported finite-subgroup classification gives
`|K|<=24`; hence `(FHC4)` is impossible.  Since the trace requirement is one
of the simultaneous hypotheses, nothing about the remaining support and
covariance rows can rescue a finite packet.

