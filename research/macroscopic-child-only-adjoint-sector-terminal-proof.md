---
rg: 2
id: macroscopic-child-only-adjoint-sector-terminal-proof
kind: route
title: Apply tracial self-copy projection equality to a hypothetical canonical microstate sequence
target: macroscopic-child-only-adjoint-sector-is-terminal
requires:
  - tracial-superoperator-self-copy-has-no-macroscopic-excess
---

If `G` were hyperlinear, choose canonical microstates.  Since `w!=1`, their
canonical trace convergence gives `||u_n(w)-1||_2^2->2`, so the amplifier
hypothesis applies.  Pass to a subsequence and a nonprincipal ultrafilter.
The positive-density child-fixed projections then become a nonzero projection
under `p_H`.  Tracial self-copy collapse puts it under `p_L`, forcing its
`q_0` displacement to vanish, contrary to the fixed lower bound `delta`.

