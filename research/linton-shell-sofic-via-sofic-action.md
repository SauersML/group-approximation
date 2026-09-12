---
rg: 2
id: linton-shell-sofic-via-sofic-action
kind: route
title: Prove the Linton shell sofic through Alekseev--Bradford sofic actions
target: linton-shell-sofic
requires: [linton-radical-sofic, linton-radical-free-action-sofic]
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

Alekseev--Bradford (*Sofic actions, halo products, and metric approximations of
groups*, arXiv:2601.18742) prove a semidirect-product theorem of the shape

> `N` sofic, `Q` sofic, and the action `Q → Aut(N)` **sofic** ⟹ `N ⋊ Q` sofic.

Apply it with `N = R`, `Q = F₀`, and `α` the splitting of the Linton shell.  The
acting group is free, hence sofic, for free; the two remaining hypotheses are
the prerequisites of this route.

This is the *only* conditional formulation in the region that is not blocked by
a refutation or a withdrawal.  It is legal precisely because its hypothesis is
on the **action** rather than on the factors:
[[sofic-semidirect-product-closure-fails]] kills every version that asks only
for the factors to be sofic, and the Kun--Thom counterexamples have amenable
normal factor and residually finite acting factor, so no strengthening on that
side can rescue those.

## The hypothesis that is not available for free

Alekseev--Bradford also give an **automatic** criterion: the action is sofic
whenever `N` is finitely generated and residually finite.  It does not apply.
Linton shows a nontrivial rationally perfect radical is infinitely generated in
the torsion-free case, which is exactly the case a counterexample to
[[one-relator-groups-sofic]] must inhabit.  So the automatic criterion covers
only the regime that was already closed by
[[residually-rationally-solvable-one-relator-sofic]], and
[[linton-radical-free-action-sofic]] has to be proved by hand.

## What the route is worth even before either prerequisite moves

It fixes the price of admission, in the same way `sofic-action-permanence` does
on the wreath lane.  The acting side is free — no obstruction there — and the
first-order action is now completely modeled:
[[one-relator-fox-magnus-descent-to-derived-linton-radical]] proves `E/R'`
residually finite.  Everything still hard is in lifting those compatible
models across the nonabelian core `R'`.  The route remains live because it asks
for the full action on `R`, not the already-settled action on `R/R'`.
