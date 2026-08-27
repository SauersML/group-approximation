---
rg: 2
id: simple-kl-via-chen-half-complexity
kind: route
title: Use Chen's universal one-half surface estimate as the final contradiction
target: kl-holds-over-two-generator-simple-groups
requires: []
artifacts:
  - research/artifacts/kl-cyclic-orbit-audit-2026-08-24.md
---

Regard each orbit relator as a unimodular word in

    N_m = (*_{i<m} S_i) * <z>

and try to contradict a minimal collapse identity using Chen's universal
surface-complexity estimate.  The attempt fails numerically at
`chen-half-complexity-does-not-force-injectivity`: the available estimate is
only `k-1>=k/2`, compatible with all `k>=2`.  The coefficient-one estimate
that would contradict the identity requires torsion-freeness or the local
`infinity`-RF hypotheses, neither of which follows for arbitrary simple `S`.

Passing to an HNN enlargement does not remove the obstruction.  For a trivial
edge group the required `infinity`-RF condition is exactly that the relevant
element have infinite order, so torsion reappears in the turn labels.
