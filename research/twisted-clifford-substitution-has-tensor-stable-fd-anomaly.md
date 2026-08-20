---
rg: 2
id: twisted-clifford-substitution-has-tensor-stable-fd-anomaly
kind: claim
title: The twisted Clifford HNN has a tensor-stable finite-dimensional HS anomaly
distinct_from:
  car-substitution-invariant-trace-emptiness-is-impossible: that proves exact invariant marked traces necessarily exist; this asks for a finite-dimensional approximation obstruction compatible with those traces.
  fixed-depth-rank-mesh-has-zero-hs-density: that rules out microscopic integrality as the anomaly; this demands a positive normalized density.
  twisted-clifford-substitution-endomorphism-gate: that supplies the exact group and nontrivial mark; this is its separate quantitative soundness gate.
---

**Open.** For the explicit finitely presented ascending HNN group produced by
`twisted-clifford-substitution-endomorphism-gate`, prove that there are
constants `epsilon_0>0` and `alpha>0` such that every finite-dimensional
unitary tuple satisfying all presentation relators with total normalized-HS
energy below `epsilon_0` sends the central mark `J` within `alpha` of the
identity.

The estimate must remain unchanged under tensor amplification.  It must also
coexist with the exact invariant marked trace supplied by
`sign-preserving-endomorphism-has-invariant-marked-trace`; consequently it
cannot be an invariant-trace-emptiness statement.

## Attempts

Arf/Pfaffian invariant-state emptiness fails by Cesaro averaging.  A fixed
integer discrepancy fails at scale `O(1/d)` and under tensor padding.  The
remaining plausible form is a positive-density local-to-global anomaly: a
fixed finite moment window whose substitution transport forces macroscopic
cross-Gram or multiplicity energy in every matrix model, despite admitting
an exact infinite-dimensional marked trace.  No such inequality is known.

