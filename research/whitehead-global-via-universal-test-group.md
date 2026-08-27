---
rg: 2
id: whitehead-global-via-universal-test-group
kind: route
title: Split coordinates of the restricted product carry vanishing back
target: whitehead-vanishing-torsion-free
requires: [whitehead-vanishing-universal-test-group, whitehead-class-supported-on-finitely-generated-subgroup]
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

## Why sufficient

Let `H` be finitely generated and torsion-free.  Pick a surjection
`F_n ->> H` with kernel `N`; then `(n,N)` indexes a coordinate of `Ufg` and
`H = F_n/N` is that coordinate.  Coordinate inclusion and evaluation give

    H ->^i Ufg ->^p H,        p . i = id_H.

Group homomorphisms induce ring homomorphisms, maps on `K_1`, and maps on
Whitehead groups, since trivial units go to trivial units.  So
`p_* i_* = id` on `Wh(H)` and `i_*` is split injective.  If
`Wh(Ufg) = 0` then `Wh(H) = 0`.

For arbitrary torsion-free `G` and `x` in `Wh(G)`, the finite-support claim
gives a finitely generated torsion-free `H <= G` and `y` in `Wh(H)` mapping
to `x`; by the previous paragraph `y = 0`, so `x = 0`.

## What this route is worth

Little, and it should be read as a boundary marker rather than a plan.  The
first paragraph is exactly what makes `whitehead-vanishing-universal-test-group`
*equivalent* to the target rather than weaker: every possible finitely
generated obstruction sits in the test group as a split summand, so the
construction contains the difficulty instead of removing it.  The route is
here because the equivalence is worth stating exactly once, and because its
contrapositive is genuinely usable -- a counterexample may always be assumed
finitely generated.
