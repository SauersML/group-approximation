---
rg: 2
id: bs-class-faithful-member-type-a-proof
kind: route
title: Glue the faithful member onto the input along a common finite-index subgroup, then apply the faithful type (A) theorem
target: bs-class-with-faithful-member-lies-in-type-a-class
requires: [faithful-finite-index-graphs-of-groups-have-type-a-overgroups, boone-higman-type-a-class-closed-under-finite-extensions, bliw-locally-finite-tree-actions-embed-in-fp-simple-groups]
---

Let `K ∈ BS_G` be arbitrary and let `H ∈ BS_G` be nontrivial and faithful on its
Bass--Serre tree.

**Step 1 (the enlargement, BLIW proof of Theorem 11.1).** Pick a vertex group `A`
of the graph of groups of `K` and a vertex group `B` of that of `H`. Both are
abstractly commensurable with `G`, so they contain finite-index subgroups
`A_0 <= A`, `B_0 <= B` and an isomorphism `A_0 ≅ B_0`. Join the two graphs of
groups by one new edge with edge group `A_0 ≅ B_0`. Call the result `L_Δ` and
`L = π_1(L_Δ)`. Every vertex and edge group of `L_Δ` is commensurable with `G`,
and every edge inclusion has finite index, so `L ∈ BS_G`. The subgraph for `K`
injects, so `K <= L`.

BLIW, arXiv:2408.05673v2, end of the proof of Theorem 11.1 (text extracted on MSI,
`/scratch.global/sauer354/orbh-lit/2408.05673.txt`, read 2026-09-18):
"HΓ ≤ LΔ is a subgraph of groups whose fundamental group acts faithfully on its
associated Bass–Serre tree. Thus, it follows from Lemma 10.1 that L acts faithfully
on its Bass–Serre tree."

Elementary check of that step. Let `N` be the kernel of `L` on its tree. It fixes
the vertex `w` carrying `B`, so `N <= L_w = B <= H`. The subgraph of groups for `H` is connected, so the `H`-translates of `w`
span an `H`-invariant subtree `H`-equivariantly isomorphic to the Bass--Serre tree
of `H`, and `N` fixes it pointwise, so `N <= ker(H on its tree) = 1`.

**Step 2 (type (A)).** The vertex groups of `L_Δ` are commensurable with the
finitely presented group `G`, hence finitely presented. The edge inclusions have
finite index and `L` is faithful. By item 1 of
`faithful-finite-index-graphs-of-groups-have-type-a-overgroups`, `L ∈ B_A`.

**Step 3.** `B_A` is closed under subgroups (item 1 of
`boone-higman-type-a-class-closed-under-finite-extensions`), so `K ∈ B_A`. Item 3
of the same node gives the finitely presented simple envelopes.

**Trust surface.** BLIW Lemma 10.1 and the rest of their Section 10 are used only
through the imported nodes. Injectivity of subgraphs of groups and the subtree
description in Step 1 are standard Bass--Serre theory, not re-read.
