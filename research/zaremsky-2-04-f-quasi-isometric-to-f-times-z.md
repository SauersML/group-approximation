---
rg: 2
id: zaremsky-2-04-f-quasi-isometric-to-f-times-z
kind: claim
title: "Zaremsky Problem 2.4 resolved: is Thompson's group F quasi-isometric to F x Z, to F x F, to T, and which quasi-retractions exist?"
root: true
distinct_from:
  thompson-f-is-not-amenable: that is the non-amenable answer to the amenability problem for F; this is Bridson's quasi-isometry question, one part of which (F quasi-isometric to T) would force that answer.
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 2, Problem 4, verbatim:
"(Bridson) Is F quasi-isometric to F × Z? (Related:) Is F quasi-isometric to
F × F? Is F quasi-isometric to T? (Surely not, but why not?) “Easier”: Does F
quasi-retract onto F × Z or F × F? Does T quasi-retract onto F?"

This claim is the question. It has six parts, one part-claim each:

- (a) `thompson-f-qi-to-f-times-z-resolved`: is F quasi-isometric to F × Z?
- (b) `thompson-f-qi-to-f-times-f-resolved`: is F quasi-isometric to F × F?
- (c) `thompson-f-qi-to-thompson-t-resolved`: is F quasi-isometric to T?
- (d) `thompson-f-quasi-retracts-onto-f-times-z-resolved`: is F × Z a quasi-retract of F?
- (e) `thompson-f-quasi-retracts-onto-f-times-f-resolved`: is F × F a quasi-retract of F?
- (f) `thompson-t-quasi-retracts-onto-f-resolved`: is F a quasi-retract of T?

It is established only through the route `zaremsky-2-04-by-all-parts`, which
requires all six part-claims. Each part-claim is itself a question, established
only by a route requiring its yes-answer or its no-answer. Never write a
`requires: []` route into this claim or into a part-claim.

**Reading.** F and T are Richard Thompson's groups (Cannon–Floyd–Parry), each
with a finite generating set and its word metric; the choice of finite
generating set changes the metric only up to bi-Lipschitz equivalence, so every
part is well posed. F × Z and F × F carry product word metrics. A metric space
`Y` is a *quasi-retract* of `X` (Alonso, "Finiteness conditions on groups and
quasi-isometries", J. Pure Appl. Algebra 95 (1994)) when there are coarsely
Lipschitz maps `i: Y -> X` and `r: X -> Y` with `r ∘ i` at bounded distance from
the identity of `Y`. Then `i` is automatically a quasi-isometric embedding.
"F quasi-retracts onto F × Z" means F × Z is a quasi-retract of F.

**Relations between the parts** (immediate from the definitions):

- a quasi-isometry is a quasi-retraction, so yes to (a) gives yes to (d), yes to
  (b) gives yes to (e), and yes to (c) gives yes to (f);
- amenability is a quasi-isometry invariant and T is not amenable, so yes to (c)
  makes F non-amenable, i.e. establishes `thompson-f-is-not-amenable`, and an
  amenable F gives no to (c).

**Background facts used by every lane on this problem.** F contains subgroups
isomorphic to F × F and to F × Z (the elements supported in `[0,1/2]` times the
elements supported in `[1/2,1]`), and F is the stabilizer in T of the base point
of the circle. So each of F, F × Z, F × F embeds in the others as a finitely
generated subgroup, and F embeds in T. Inclusions of finitely generated subgroups
are coarse embeddings, so invariants that are monotone under coarse embeddings
cannot separate F, F × Z and F × F.

## Attempts

- 2026-09-13 (lane z2-04-f-qi): region opened with the six part-claims. Invariants
  that cannot separate F from F × Z or F × F are being recorded as fences on the
  part-claims; the amenability reduction for (c) is recorded as a route.
