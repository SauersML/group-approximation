---
rg: 2
id: x2-witnesses-are-never-group-shaped
kind: claim
title: Finitely generated X(2) witnesses cannot be group algebras, amenable crossed products, or canonical-trace group ranges
artifacts:
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
---

Suppose Problem X(2) fails, and let `(A, τ)` be a finitely generated
weakly dense witness inside `R` as produced by
`stw10-x2-reduces-to-finitely-generated-weakly-dense-witnesses`
(faithful amenable non-QD trace, GNS von Neumann algebra `R`, not
both exact and UCT).  Then:

1. `A` is not trace-isomorphic to any reduced group C\*-algebra with
   its canonical trace;
2. `A` is not trace-isomorphic to any reduced crossed product
   `C(X) ⋊_r G` of a topologically amenable action with an
   invariant-measure trace;
3. no generating tuple of unitaries of `A` generates a nonamenable
   subgroup of `U(A)` with `δ_e` joint `τ`-distribution.

Thus canonical-trace group mechanisms are invisible here: generators of a
witness cannot have the regular `delta_e` moment pattern of a nonamenable
group, and the reduced-group / amenable-action constructions in (1)--(3)
are barred.  This does NOT exclude a group-generated image coming from a
noncanonical faithful hyperfinite character `chi`, for which
`chi(g) != 1` but possibly `chi(g) != 0` away from the identity.  In
particular, the live route
`non-mf-subgroup-of-hyperfinite-factor-unitary-group` is not covered by
this theorem; it asks for exactly such a noncanonical character.
