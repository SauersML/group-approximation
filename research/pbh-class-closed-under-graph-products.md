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
  - research/artifacts/gq-bh-bh-free-10-verify-graph-products.md
---

**ESTABLISHED** through `pbh-graph-product-closure-proof`. Re-verified end to
end on 2026-09-18 by lane bh-free-10 (`gq-bh-bh-free-10-verify-graph-products`):
every step of the route checks. BFFHZ Theorem C, Theorem E, the proof of
Corollary F, and Question 3.1 were re-read in the arXiv:2503.21882v2 TeX source,
and they match what the route uses. A second, independent step-by-step re-check on 2026-09-18 by lane bh-free-11
(`gq-bh-bh-free-11-graph-product-verification`) also found no gap. Both are internal
verifications, not an external review. Referee PASS by bh-ref-kourovka-b on 2026-09-18 (see Referee). Priority search is partial: FFWZ arXiv:2603.24687 (extracted
text on MSI) never mentions graph products, no node here treats them, and arXiv
API queries of 2026-09-14 and 2026-09-18 ("graph product" AND "Boone") returned
no entries.

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

## Referee (bh-ref-kourovka-b, 2026-09-18): PASS

**Verdict: PASS.** I read `pbh-graph-product-closure-proof` line by line. It answers BFFHZ Question 3.1
positively. The construction is short and elegant: in `Aut_H(H * F_2)`, transvections of `x` carry
`K * L` faithfully, and a twisted conjugation `γ_c` supplies `C`, acting correctly on both at once.
Credit to its author (09-14) and to the two re-checks, bh-free-10 and bh-free-11.

**Sources.** I read the BFFHZ TeX (`gq/src/bh-free-24/bffhz.tex`) directly.
- The question under "The question it answers" is verbatim (l.453).
- Theorem C (`thrm:mif_pbhc`, (i)⇔(iv)) and Theorem E (`thrm:autg_pbhc`: for fp simple MIF `G` and
  `n ≥ 2`, `Aut_G(G*F_n)` admits a type (A) action) are used exactly as stated.

**Step checks.**
- **Step 0.** `A` is fp and embeds in `SV_A`, which is fp and simple, so `A` has solvable word
  problem and Theorem C applies to it. Direct products stay in `B_A`: take the action on
  `S_1 ⊔ S_2`, whose stabilizers `Stab × A_2` are f.g.
- **Steps 1–2.**
  - `ρ_a ρ_b = ρ_{ab}` because `ρ_a` fixes `b ∈ H * ⟨y⟩`.
  - `γ_c γ_d = γ_{cd}` on `x` and on `y`.
  - Both are automorphisms, with inverses `ρ_{a^{-1}}` and `γ_{c^{-1}}`.
- **Step 3.** (GP1) holds on `x`, on `y` and on `H`. Both cases use exactly that `C` and `K` commute
  in `H`.
- **Step 4.** The universal property of `L ⋊ C`, of `C × K` and of the amalgam. Correct.
- **Step 5.**
  - `G = N ⋊ C` with `N = ⟨K, L⟩`, because `C` normalizes both and `R(nc) = c`.
  - `N ≅ K * L` by the amalgam normal form, since `K ∩ C = 1 = L ∩ C`.
  - `w` sends reduced words to reduced words in `H * ⟨y⟩`.
  - `Φ(nc)(y) = c^{-1} y c` forces `c = 1`.

  Correct.
- **Step 6.** The retraction of a graph product onto an induced subgraph, and
  `G_Γ = G_{Γ∖v} *_{G_{lk v}} (G_{lk v} × G_v)`, are standard and correct. An empty link gives a free
  product, which is also covered.
- **Hypotheses of Q3.1.** The vertex groups satisfy PBH, so they are f.g. The graph product is then
  f.g., embeds in a group of type (A), and so has solvable word problem (Kuznetsov). That is exactly
  PBH in BFFHZ's sense.

**Notes** (none affects the verdict).
1. **Scope.** Part 1 needs `K` to commute with `C`. The node's Scope section says so correctly.
2. **Priority** (searched 2026-09-18, web). I found no treatment of graph products under PBH or BH
   beyond the cographs covered by BFFHZ Corollary F and Zaremsky.
