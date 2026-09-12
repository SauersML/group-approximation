---
rg: 2
id: signed-hecke-simultaneous-holonomy-route
kind: route
title: Compose the explicit one-marginal escape cells into the balanced cycle atlas
target: signed-hecke-block-escaping-cycle-holonomy
requires:
  - one-binary-marginal-block-escape
  - feasible-chord-collision-has-free-phase-block-escape
  - finite-chord-context-is-joint-table-plus-collision
  - global-chord-target-selection-is-fixed-profile-boundary-bcs
  - simultaneous-block-escaping-context-holonomy
---

Apply the simultaneous construction to the rationally balanced context
packets.  Its common context unitaries are the `V_c` in `(BCH1)`, and the
preserved marginals are exactly `(BCH2)`.  The retained non-root atom meets
the escape requirement.  The second established input closes every
intermediate chord whose conditional-rank table is feasible and whose frozen
fiber retains a genuine assignment collision; the open simultaneous input is
therefore needed only for the residual collision-free/infeasible cells and
their common-context compatibility.  Thus the clauses establish the full balanced
cycle-holonomy claim.
