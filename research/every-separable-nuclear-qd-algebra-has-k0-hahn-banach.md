---
rg: 2
id: every-separable-nuclear-qd-algebra-has-k0-hahn-banach
kind: claim
title: Every separable nuclear quasidiagonal C*-algebra has the K_0-Hahn-Banach property
distinct_from:
  brown-dadarlat-qd-extensions-and-k0-hahn-banach: that is the established equivalence theory and the definition; this is the open universal property.
  k0-hahn-banach-for-boundary-singular-classes: that is the boundary case under the extra hypothesis that all traces are quasidiagonal; this is the property for every separable nuclear quasidiagonal algebra and every singular class.
artifacts:
  - research/artifacts/stw07-k0-hahn-banach-trace-sign-2026-09-11.md
---

**OPEN.**  For every separable nuclear quasidiagonal `A` and every
`x in K_0(A)` with `Zx cap K_0^+(A) = {0}`, there are asymptotically
multiplicative, asymptotically isometric c.c.p. maps `phi_n: A -> M_(k_n)` with
`(phi_n)_*(x) = 0` for large `n` (Brown--Dadarlat, Definition 4.8).

By `brown-dadarlat-qd-extensions-and-k0-hahn-banach` (Theorem 4.11) this is
equivalent to the QD extension property for the whole class.  It therefore
proves the Blackadar--Kirchberg problem for extensions with UCT quotient.
It is implied by STW Problem VII.

## Attempts

- **Trace-sign decomposition.**  Route
  `k0-hahn-banach-from-traces-and-boundary` splits the property.  Singular
  classes changing sign on quasidiagonal traces are killed.  Singular classes
  are never strictly one-signed on all traces.  What remains is (i) the exact
  residual of X(1), so that all traces are quasidiagonal, and (ii) the
  boundary case.
- **Necessity of (i) for this route.**  If some algebra has a class positive
  on quasidiagonal traces but not on all traces, the property fails outright
  (`stw07-qd-trace-positive-class-kills-qd-extension`).  So the exact X(1)
  residual cannot simply be dropped from the route.
