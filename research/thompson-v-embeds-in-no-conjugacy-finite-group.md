---
rg: 2
id: thompson-v-embeds-in-no-conjugacy-finite-group
kind: claim
title: Thompson's group V embeds in no group with finitely many conjugacy classes, so not every decidable group has a conjugacy-finite overgroup
distinct_from:
  every-wp-group-embeds-in-fp-conjugacy-finite-group: that is the universal premise asserting a finitely presented conjugacy-finite overgroup for every decidable input; this is the counterexample at the input V, which refutes it.
  conjugacy-finite-recursive-presentation-solvable-wp: that proves conjugacy finiteness forces a solvable word problem, which is consistent with the premise; this uses the same finiteness against element orders, which the premise cannot survive.
  universal-fiber-product-data-for-word-problem-groups: that allows the conjugacy-finite normal subgroup N to be proper, and it survives this claim; this rules out only the case N = T, where the whole overgroup has finitely many conjugacy classes.
artifacts:
  - research/artifacts/hl-bh-universal-route-map-2026-09-13.md
---

**ESTABLISHED** (elementary; not independently reviewed; no novelty claimed).

1. A group with `k` conjugacy classes has at most `k` distinct element orders.
2. Thompson's group `V` contains an element of order `n` for every `n >= 1`,
   and it is finitely generated with solvable word problem.
3. Hence `V` is a subgroup of no group, finitely presented or not, with finitely
   many conjugacy classes.

Consequently `every-wp-group-embeds-in-fp-conjugacy-finite-group` is false: its
universal quantifier fails at `G = V`. The route
`fiber-product-data-from-conjugacy-finite-overgroup` is dead.

The general fiber-product premise `universal-fiber-product-data-for-word-problem-groups`
is not refuted. It only asks for finitely many `T`-conjugacy classes inside a
normal subgroup `N`, and item 1 then says only that `N` has finitely many element
orders. Every torsion element of the input that lies in `N` has one of those
orders; elements outside `N` are unconstrained.

The same obstruction applies to every input with infinitely many distinct
element orders, for instance every group containing `V` or Thompson's `T`.

DERIVATION
thompson-v-conjugacy-finite-obstruction-proof
