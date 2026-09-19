---
rg: 2
id: unsquared-defect-mf-invisible-via-finite-packet-holonomy
kind: route
title: Pull the eight-lamp common-carrier certificate back across the invisible sign
target: unsquared-defect-mf-invisible
requires:
  - literal-central-mark-corona-invisible
  - literal-unsquared-defect-finite-packet-holonomy
artifacts:
  - research/artifacts/literal-eight-lamp-finite-packet-holonomy-2026-08-26.md
  - GroupApproximation/Sofic/LiteralSignFreeQuotient.lean
---

Let `Theta:E->U(Q)` be any norm-matrix-corona homomorphism.  By
`literal-central-mark-corona-invisible`, `Theta(w)=1`, so `Theta` factors
through `q:E->E/<w>`.  The finite-packet holonomy theorem kills `q(u)` in
every such factor representation.  Hence `Theta(u)=1`.  Since `Theta` was
arbitrary, `u` lies in `Rad_MF(E)`, and normality of all kernels gives
`<<u>>^E<=Rad_MF(E)`.

Unlike the original route to this target, this proof does not invoke the
commuting-involution collapse endpoint.  Its analytic input is the
eight-lamp packet's exact rank floor and authenticated common-carrier return.

