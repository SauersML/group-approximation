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

- **Trace-sign theorems settle only trace-visible classes.**  Singular classes
  changing sign on quasidiagonal traces are killed
  (`stw07-sign-changing-qd-trace-values-kill-class`).  So are classes
  vanishing on a trace whose UCT kernel quotient sees them rationally
  (`stw07-quotient-trace-zero-nontorsion-class-is-killed`).  But
  `stw07-trace-invisible-classes-carry-hahn-banach` makes every class
  trace-invisible in `(A tensor K)~` without changing whether it is killed.
  So the property is exactly a statement about trace-invisible classes, and
  route `k0-hahn-banach-from-traces-and-boundary` is only a restatement.
- **Obstruction side.**  If some algebra has a singular class positive on its
  quasidiagonal traces, the property fails outright
  (`stw07-qd-trace-positive-class-kills-qd-extension`).  That requires a
  nonquasidiagonal trace and a non-UCT nuclear quotient
  (`stw07-trace-obstruction-forces-nonqd-trace-and-non-uct`).
