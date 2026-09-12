---
rg: 2
id: sofic-semidirect-product-closure-fails-proof
kind: route
title: Read the closure failure off the Kun--Thom wreath products
target: sofic-semidirect-product-closure-fails
requires: [kun-thom-nonsofic-wreath]
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

## Direct proof

Take `Γ < G` from the prerequisite's Theorem E — residually finite Kazhdan
groups with `Γ` infranormal and not normal.  Theorem A makes
`( ⊕_{G/Γ} Z/2Z ) ⋊ G` nonsofic.  Its normal factor is abelian, hence amenable,
hence sofic; its acting factor is residually finite, hence sofic.  So a
semidirect product of two sofic groups need not be sofic.

The step from the prerequisite is small but not empty: it discards the specific
groups and keeps a closure property of the class, which is the form every route
in this region consumes.  Recording it separately is what lets a route be killed
by reference to a permanence failure instead of by re-deriving a wreath-product
counterexample each time.
