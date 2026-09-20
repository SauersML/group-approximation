---
rg: 2
id: thompson-f-no-two-transitive-via-square-root-closure
kind: route
title: No 2-transitive action of F, because a 2-transitive point stabilizer is a maximal subgroup of infinite index containing the square of an element outside it
target: thompson-f-has-no-faithful-2-transitive-action
requires:
  - thompson-f-maximal-subgroups-are-square-root-closed
  - thompson-f-two-transitive-actions-are-faithful
---

Suppose `F` acts 2-transitively on `Ω` with `|Ω| ≥ 3`. Fix `ω ∈ Ω` and put `H = F_ω`.

1. **`H` is maximal.** A 2-transitive action is primitive, so point stabilizers are maximal.
2. **`H` has infinite index.** By `thompson-f-two-transitive-actions-are-faithful` (item 2),
   `Ω` is infinite, so `[F : H] = |Ω| = ∞`.
3. **`H` is not square-root closed.** Take `ω' ≠ ω`. By 2-transitivity there is `x` with
   `(xω, xω') = (ω', ω)`. Then `x ∉ H`, and `x²ω = xω' = ω`, so `x² ∈ H`.

Item 3 contradicts `thompson-f-maximal-subgroups-are-square-root-closed` applied to `H`. So no
2-transitive action on at least 3 points exists, which is the target.

**Relation to the other route.** `thompson-f-no-two-transitive-via-disagreement-set-type` splits on
the topology of the disagreement set. This route instead reduces the target to a single
statement about all maximal subgroups of infinite index.

**Status of the prerequisite.** The conjecture holds in the stronger relatively convex form for
every maximal subgroup of infinite index that is given explicitly in the literature, by
`jones-subgroup-coset-spaces-carry-invariant-orders`. It is open in general.
