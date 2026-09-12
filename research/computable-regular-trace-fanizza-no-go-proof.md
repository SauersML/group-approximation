---
rg: 2
id: computable-regular-trace-fanizza-no-go-proof
kind: route
title: Enumerate group-algebra zero and decide HALT versus NONHALT
target: computable-regular-trace-fanizza-return-would-decide-halting
requires:
  - fanizza-heat-filter-has-uniform-cstar-decay
---

Use `(RHC2)` and the regular heat bound to obtain `(CRF1)--(CRF3)` on every
NONHALT instance; use `(RHC1)` for `(CRF4)` on HALT instances.  The finite
support partition enumeration after `(CRF5)` proves that group-algebra zero
is recursively enumerable for uniformly recursively presented groups.
Hence both a set and its complement would be recursively enumerable.

