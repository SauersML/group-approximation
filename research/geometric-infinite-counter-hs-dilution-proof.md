---
rg: 2
id: geometric-infinite-counter-hs-dilution-proof
kind: route
title: Count the counter head and the cyclic wraparound boundary
target: geometric-infinite-counter-is-hs-trace-diluting
requires: []
---

On `C^D tensor C^m`, the head projection is `q_0 tensor I_m`, of rank `m`
inside dimension `Dm`; this proves `(ICT1)`.  The projection onto the last
`ell` counter sites has rank at most `ell m`, hence normalized trace at most
`ell/D` and normalized `2`-norm at most `sqrt(ell/D)`.

Replace unilateral increment by cyclic increment.  A word containing at most
`ell` increments and decrements acts identically to its unilateral version
on every basis path which never meets the wraparound boundary.  Therefore the
difference of the two word operators is supported on the boundary projection
(on one or both sides).  A telescoping estimate changes only the harmless
constant depending on the fixed word, and its normalized HS norm tends to
zero as `D->infinity`.

Finally `|psi_D><psi_D| tensor I_m` has rank `m`, whatever the coefficients
of the unit vector `psi_D`; its normalized trace is again `1/D`.  Replacing
`m` by any other amplification multiplicity cancels from the same quotient.
This proves the trace-dilution and finite-truncation assertions and hence the
claimed firewall.
