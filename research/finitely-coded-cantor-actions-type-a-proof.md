---
rg: 2
id: finitely-coded-cantor-actions-type-a-proof
kind: route
title: The degree-category comparison lemma never used finiteness of the unit groups, so the clopen type (A) argument runs for any finitely coded groupoid with a finitely presented stabilized full group
target: finitely-coded-cantor-actions-give-type-a-hosts
requires: [degree-category-comparison-type-a-proof, stabilized-kgraph-full-group-clopen-action-proof, type-a-action-gives-boone-higman-for-subgroups, boone-higman-type-a-class-closed-under-finite-extensions]
---

**Item 1.** Steps 1–2 of `degree-category-comparison-type-a-proof` use only four
facts:
- `Z(λu) = Z(λ)` for units `u`;
- the partition of a cylinder by the degree-`ε_j` extensions of its source, taken
  modulo units, which is finite by the local finiteness hypothesis and disjoint by
  (UFP*);
- finite alignment, so that clopen sets are finite disjoint unions of cylinders,
  since the common extensions of `λ` and `μ` of degree `max(d(λ), d(μ))` are finitely
  many modulo units;
- the two Cuntz loops.
Finiteness of the unit groups is not used. Strong connectivity within pieces spreads
the support. The Cuntz colour duplicates a cylinder before it is refined, and raises
counts. So two nonempty clopen sets in one piece have decompositions with the same
count vector, and prefix replacements match them.

**Item 2.** With item 1, Steps 3–4 of `degree-category-comparison-type-a-proof` (the
same as Steps 4–5 of `stabilized-kgraph-full-group-clopen-action-proof`) give:
- faithfulness;
- finitely many orbits of pairs, recorded by atoms and pieces;
- finitely presented stabilizers, which are products of direct factors of `D`;
- finite presentation of `D`, by hypothesis.

**Item 3.** Zaremsky's Corollary B (`type-a-action-gives-boone-higman-for-subgroups`),
the embedding `g ↦ g x id` of `F(𝒢)` in `D`, and closure of `B_A` under subgroups.

**Limits.** The word-problem bound is the count in
`finite-k-graph-full-groups-have-exponential-word-problem` (tables of prefix
replacements grow at most exponentially). With unit groups present, each step also
multiplies unit elements. The central-extension limit is the remark and item 1 of
`central-extension-untwisting-over-boundaries`. A central extension `C` of a coded
`C̄`, reached through the `C̄`-space, acts on a free `A`-cover of it, which is a skew
product. That is impossible when the class survives on stabilizers.
