---
rg: 2
id: exact-group-algebra-from-witness
kind: route
title: Combine exact extension permanence with the non-MF witness
target: exact-stably-finite-non-mf-reduced-group-algebra
requires: [sofic-non-mf-witness]
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Endpoint/NonMFImpact.lean
---

## Why sufficient

The locally finite lamp kernel is amenable and exact.  The quotient
`V <= GL_4(Q)` is exact by the exactness theorem for linear groups.  Exact
groups are closed under extensions, and group exactness is equivalent to
exactness of the reduced group algebra.  The canonical reduced trace is
faithful and forces stable finiteness in all finite matrix amplifications.
An MF embedding of `C*_r(W)` would restrict to a faithful corona model of
`W`, contradicting `sofic-non-mf-witness`.  Exactness is literature-backed;
the remaining assertions have the cited closed Lean endpoint.
