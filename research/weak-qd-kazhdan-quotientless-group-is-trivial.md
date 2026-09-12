---
rg: 2
id: weak-qd-kazhdan-quotientless-group-is-trivial
kind: claim
title: A weakly quasidiagonal Kazhdan group without finite quotients is trivial
artifacts:
  - research/artifacts/operator-mf-weak-quasidiagonality-audit-2026-09-11.md
distinct_from:
  mf-kazhdan-group-without-finite-quotients-is-trivial: this assumes unital completely positive approximations of the full group C-star algebra; the operator-MF version has no such hypothesis and needs an additional bridge
---

Let `G` be a countable group with property (T). Suppose that there is an
asymptotically multiplicative sequence of unital completely positive maps
`phi_n:C*(G)->M_(d_n)` with
`limsup_n ||phi_n(u_g)-I|| > 0` for every `g!=1`.
If every homomorphism from `G` to a finite group is trivial, then `G=1`.

In particular, an infinite hyperbolic Kazhdan group without finite
quotients is not weakly quasidiagonal.
