---
rg: 2
id: pbh-class-closed-under-graph-products
kind: claim
title: The permutational Boone--Higman class is closed under graph products over finite graphs and under amalgams X *_C (C x K) over retracts C of X
distinct_from:
  aut-free-groups-satisfy-permutational-boone-higman: that imports BFFHZ Theorem A with Corollary F, closure under free products; this proves closure under graph products, which contain free products (edgeless graphs) as one special case, and answers BFFHZ Question 3.1.
  boone-higman-type-a-class-closed-under-finite-extensions: that is closure under finite direct products, subgroups and finite-index overgroups; this is closure under graph products and retract amalgams, of which direct products (complete graphs) are the other special case.
  pbh-class-closed-under-relative-holomorphs: that is closure under relative holomorphs of M * F_m and partial-conjugation mapping tori; this is closure under amalgams over retracts with a commuting factor, a different construction realized by a twisted conjugation of a second letter.
  permutational-boone-higman-closed-under-wreath-products: that is closure under restricted permutational wreath products over G-sets with finite point stabilizers; this is closure under graph products, whose retract decomposition is a free, not direct, base with infinite stabilizers.
  boone-higman-closed-under-finite-direct-products: that is the open product closure of the Boone--Higman class itself; this is a theorem about the permutational class B_A only.
artifacts:
  - research/artifacts/gq-bh-bh-free-11-graph-product-verification.md
  - research/artifacts/ideas-bh-round2-2026-09-14.md
---

**ESTABLISHED** through `pbh-graph-product-closure-proof`. Not externally reviewed; adversarially re-checked step by step on 2026-09-18 by lane bh-free-11 (all steps and imports hold; `research/artifacts/gq-bh-bh-free-11-graph-product-verification.md`). Priority search is partial: FFWZ arXiv:2603.24687 (extracted text on
MSI) never mentions graph products, no node here treats them, and an arXiv API
query of 2026-09-14 returned no entries.

Write `B_A` for the class of groups that embed in a group admitting an action of
type (A) (`boone-higman-type-a-class-closed-under-finite-extensions`); in the
language of BFFHZ these are the groups satisfying the permutational
Boone--Higman conjecture.

## Statement

1. **Retract amalgams.** Let `X, K ∈ B_A` and let `C <= X` be a retract of `X`.
   Then the amalgamated product `X *_C (C × K)` is in `B_A`. With `K = Z` this is
   the centralizing HNN extension `< X, t | t c = c t (c ∈ C) >`.
2. **Graph products.** Let `Γ` be a finite simplicial graph with vertex groups
   `G_v ∈ B_A`. Then the graph product `G_Γ` is in `B_A`. So `G_Γ` embeds in a
   finitely presented simple group, and if it is finitely generated its word
   problem is solvable (`type-a-action-gives-boone-higman-for-subgroups`).

## The question it answers

Belk--Fournier-Facio--Hyde--Zaremsky, arXiv:2503.21882v2, extracted text on MSI
(`bh-reviewer/2503.21882.txt`, l.680--681), verbatim: "Question 3.1. Let G be a
graph product over a finite graph such that each vertex group satisfies PBH.
Does G satisfy PBH?" Part 2 answers it yes.

Their next paragraph (l.682--687) explains why general amalgams are excluded:
the word problem of an amalgam is tied to membership in the amalgamated
subgroup. Part 1 avoids this because a retract has decidable membership and a
normal complement.

## What is new

- Over cographs (graphs built by joins and disjoint unions) graph products are
  iterated direct and free products, already covered by Zaremsky Proposition 5.5
  and BFFHZ Corollary F.
- The first new graph is the path `P_4`. For example, the `P_4` graph product of
  four copies of Thompson's group `V`, of `Aut(F_n)`, or of finitely presented
  twisted Brin--Thompson groups embeds in a finitely presented simple group.
  Graph products with vertex groups `Z` or `Z/2` (right-angled Artin and Coxeter
  groups) were known.

## Scope

- Part 1 needs `C` to be a retract of `X` and to commute with `K`. Twisted
  retract amalgams `X *_C (K ⋊ C)` are not covered.
- Nothing here reaches `Out(F_n)` or closed-surface mapping class groups.
