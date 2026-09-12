---
rg: 2
id: whitehead-class-supported-on-finitely-generated-subgroup
kind: claim
title: Every Whitehead class comes from a finitely generated subgroup
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

For any group `G` and any `x` in `Wh(G)` there are a finitely generated
subgroup `H <= G` and a class `y` in `Wh(H)` whose image under the inclusion
is `x`.  If `G` is torsion-free then so is `H`.

Elementary: a matrix and its chosen inverse involve finitely many group
elements between them, and the subgroup those generate already carries both
matrices and the two inverse identities.

This is the reason every reduction of `whitehead-vanishing-torsion-free` may
assume finite generation, and it is used by both routes into that root.  It
is worth naming rather than inlining because the two routes use it for
different purposes -- one to reach a coordinate of a restricted product, one
to bound the finite pattern that gets transplanted -- and because the "and
its inverse" is load-bearing: finite support of `A` alone would not do, since
`K_1` representatives must be genuinely invertible.
