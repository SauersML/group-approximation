---
rg: 2
id: some-fp-group-acts-on-the-rado-graph-with-type-a
kind: claim
title: Some finitely presented group acts on the Rado graph by automorphisms with a type (A) action on its vertices
distinct_from:
  type-a-action-gives-boone-higman-for-subgroups: that is Zaremsky's payoff for a type (A) action on any set; this asks for a type (A) action whose set carries an invariant Rado graph, a host not built on Cantor charts.
  v-invariant-clopen-graphs-are-never-the-rado-graph: that rules out V acting on single clopen sets; this is the existence question itself.
  some-v-invariant-graph-on-clopen-tuples-is-rado: that is the special case G = V on a clopen tuple sort, which implies this; this allows any finitely presented group and any vertex set.
artifacts:
  - research/artifacts/hl-bh-fraisse-thompson-2026-09-14.md
---

**OPEN.** Some finitely presented group `G` acts faithfully on the vertex set of the Rado
graph `R` by graph automorphisms, with finitely generated point stabilizers and finitely
many orbits of two-element vertex sets.

## Why it matters

- Such an action is of type (A). So every subgroup of `G` has solvable word problem and embeds
  in a finitely presented simple group (`type-a-action-gives-boone-higman-for-subgroups`,
  Zaremsky's Corollary B).
- This is idea 4 ("Fraïssé Thompson groups") of
  `research/artifacts/ideas-bh-round2-2026-09-14.md`: F, V and T are finitely presented dense
  actors on the ω-categorical structures (Q,<), the atomless Boolean algebra and the circular
  order.

## Scope caveat

Existence alone adds Boone–Higman inputs only when `G` contains groups not already inside
known type (A) actors. If `G = V`, via route `rado-type-a-action-from-v-tuple-sort`, it adds
none.

## Attempts

1. **V on single clopen sets.** Impossible, by `v-invariant-clopen-graphs-are-never-the-rado-graph`.
2. **Piecewise automorphisms (unproved, recorded in the artifact).** The V-analogue for `R`
   would glue isomorphisms along finite partitions of the vertex set into induced copies of
   `R`. Such permutations need not preserve edges between different parts, so they are
   permutations of the vertices, not automorphisms of `R`.
   - Cameron's chapter (arXiv:1301.7544, Theorem 11, quoted in the artifact) lists the five
     closed overgroups of `Aut(R)`.
   - No chart for prefix replacement inside `Aut(R)` is known here.
