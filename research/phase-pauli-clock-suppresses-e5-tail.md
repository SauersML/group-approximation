---
rg: 2
id: phase-pauli-clock-suppresses-e5-tail
kind: route
title: Use local phase-Pauli transports to preserve the accumulated pulse prefix
target: packet-hard-transport-preserves-pulse-prefix
requires:
  - cyclic-phase-pauli-shears-have-unbounded-clock-order
  - finitely-presented-phase-pauli-polynomial-prefix-clock
---

Use the unbounded polynomial clock to enumerate the pulse signs and the
level-local centralizer relation `(FPP1)` to place each transported forbidden
packet inside the old positive prefix.  Polynomial derivation area is
permitted because the resulting error is summed against the contractive
Fanizza weights.
