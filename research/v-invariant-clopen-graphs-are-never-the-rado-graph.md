---
rg: 2
id: v-invariant-clopen-graphs-are-never-the-rado-graph
kind: claim
title: No graph on the proper nonempty clopen subsets of the Cantor set invariant under Thompson's group V is the Rado graph
distinct_from:
  fp-full-binary-cantor-groups-have-type-a-actions: that establishes the type (A) action of finitely presented full Cantor groups on clopen sets and counts its pair orbits; this shows that no invariant graph on that same set is the Rado graph, so that action is not a type (A) action on the Rado graph.
  some-fp-group-acts-on-the-rado-graph-with-type-a: that is the open existence question for a finitely presented type (A) actor on the Rado graph; this rules out its most natural candidate, V acting on single clopen sets.
artifacts:
  - research/artifacts/hl-bh-fraisse-thompson-2026-09-14.md
  - experiments/bh-fraisse-rado/fraisse-rado-certs.py
  - experiments/bh-fraisse-rado/fraisse-rado-verify.py
  - experiments/bh-fraisse-rado/certs.jsonl
  - experiments/bh-fraisse-rado/verify.txt
---

**ESTABLISHED** through `v-invariant-clopen-graph-rado-census-proof`. Computer-checked
census with two independent implementations; not independently reviewed; no novelty claimed.

## Claim

Let `C` be the Cantor set, `X` the countable set of nonempty proper clopen subsets of `C`,
and `D` any group with `V <= D <= Homeo(C)`, acting on `X`. Every `D`-invariant graph `Γ`
on `X` fails the three-point extension property. That is, there are distinct
`U_1, U_2, U_3 ∈ X` and `v ∈ {0,1}^3` such that no `z ∈ X \ {U_1, U_2, U_3}` has
`(z ~ U_i) = v_i` for every `i`. So no `D`-invariant graph on `X` is isomorphic to the
Rado graph.

## Sharpness

The invariant graphs are the 32 unions of five pair classes: complementary, disjoint,
nested, covering overlap, generic overlap. The empty and complete graphs fail the one-point
property. Exactly 8 of the other 30 satisfy the two-point extension property:
- disjoint ∪ nested;
- nested ∪ covering overlap;
- disjoint ∪ generic overlap;
- covering overlap ∪ generic overlap;

each with or without the complementary class. All 8 fail at three points.

## Why

- **Complement correlation.** For a complementary pair `{U, U^c}`, the class of `(U^c, z)`
  is determined by the class of `(U, z)`:
  - `z ⊂ U^c` disjoint from `U` ↔ nested in `U^c`;
  - `U ⊂ z` nested ↦ covering overlap with `U^c`;
  - covering overlap ↦ nested;
  - generic ↦ generic.

  So adjacency to `U` and to `U^c` is tied for every invariant graph. This kills 22 of the
  30 at two points, with certificate family `{U, U^c}`.
- **The 8 survivors** die on `{(a ∪ b)^c, a, a^c}` or `{(a ∪ b)^c, a, b^c}` for disjoint
  cones `a, b` (`verify.txt`).
- **Complement symmetry.** `U ↦ U^c` commutes with `D`, swaps disjoint with covering overlap,
  and fixes the other classes. The survivor list is closed under it.

## Consequence

The natural type (A) action of `V`, and of every finitely presented full Cantor group
containing `V`, carries no invariant Rado graph. A "Fraïssé Thompson group" for the Rado
graph (idea 4 of `research/artifacts/ideas-bh-round2-2026-09-14.md`) has to act on a
different set. The next finite search is `some-v-invariant-graph-on-clopen-tuples-is-rado`.
