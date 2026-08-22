---
rg: 2
id: long-bs14-packet-threshold-counterexample-proof
kind: route
title: Adjacent fourth-power clocks are HS-close but irreducibly operator-far
target: long-bs14-packets-defeat-invariant-op-thresholding
requires:
  - bs14-unitary-representations-are-periodic-cycle-packets
  - bs14-residual-invariant-hull-has-unbounded-packet-loss
---

Equations `(LPT1)--(LPT2)` are the scalar cycle packets from the first
required claim.  The geometric-series estimate proves `(LPT3)`.  The final
point of the doubled orbit lies at circle distance at least `1/4` from the
entire undoubled orbit, proving `(LPT4)` by spectral variation.

Only the final `O(log(1/theta))` orbit coordinates exceed a fixed mismatch
threshold.  Transitivity of the cycle shift makes the invariant hull of any
one of them the whole packet, exactly the mechanism isolated abstractly by
the second required claim.  Irreducible multiplicity uniqueness proves the
full-rank exact-padding statement.
