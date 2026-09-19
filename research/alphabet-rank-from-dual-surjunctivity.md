---
rg: 2
id: alphabet-rank-from-dual-surjunctivity
kind: route
title: An alphabet-enlarging cover precomposed with a collapsing letter map is a dual failure
target: post-surjective-automata-never-enlarge-the-alphabet
requires:
  - every-group-is-dual-surjunctive
  - alphabet-enlarging-covers-refute-dual-and-domain-duality
---

Group by group. Suppose `P : A^G → B^G` is strongly post-surjective with `|B| > |A|`. Relabel so that `A ⊊ B`.
Part 1 of `alphabet-enlarging-covers-refute-dual-and-domain-duality` makes `P ∘ q^G` a post-surjective,
non-pre-injective self-map of `B^G`. That contradicts `every-group-is-dual-surjunctive` at `G`.

Parts 2 and 3 of the same claim give the same implication from
`constant-point-sft-domains-admit-no-post-surjective-covers` and from `proper-sft-domains-admit-no-dual-failures`.
So NPE holds on every sofic group, via Doucha–Gismatullin, and on every group where any of the three holds.
