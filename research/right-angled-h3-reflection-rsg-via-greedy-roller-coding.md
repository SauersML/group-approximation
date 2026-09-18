---
rg: 2
id: right-angled-h3-reflection-rsg-via-greedy-roller-coding
kind: route
title: Code the Roller boundary of the right-angled tiling by the memoryless rule "reflect in the smallest-labelled separating face plane"; states are cells of one tile's face-circle arrangement (refined by cosets for subgroups); irreducibility is conditions (a)–(c), contraction is the carrier-entry lemma
target: right-angled-reflection-groups-in-h3-are-contracting-rsgs
requires:
  - closed-surface-groups-contracting-rsg-via-bowen-series
  - contracting-rsgs-closed-under-finite-index-overgroups
  - sft-irreducible-core-iff-unique-recurrent-component
---

Lane `bh-partials`, lane proof, not reviewed.

**Notation.**
- `P_j` is the plane of face `j` of `F`, and `s_j` the reflection in it.
- The **walls** are the `W`-translates of the `P_j`. Right angles make every face plane a union of faces of the
  tiling `W·F`.
- The tile graph is the Cayley graph of `(W, {s_j})`. Its distance counts separating walls (chamber distance of a
  Coxeter complex).
- **Classical facts used.**
  - Two walls are either orthogonal or ultraparallel. Asymptotic distinct walls would give, after translating by `W`,
    infinitely many pairs of walls at distance → 0 near a compact set, contradicting local finiteness.
  - Non-adjacent faces of `F` have ultraparallel planes (Andreev).
  - Pairwise adjacent faces share a vertex (compact right-angled polyhedra have no prismatic 3-circuits).
- **The coding space.** `X` is the dual CAT(0) cube complex of the walls, and `∂X` its Roller boundary: the non-principal
  consistent choices of a side of every wall. It is compact and totally disconnected, and `W` acts on it by
  homeomorphisms. For `ω ∈ ∂X` write `ω ∈ D̂_j` if `ω` chooses the far side of `P_j` from `F`.

**Step 1 (the greedy Markov map).**
- For `ω ∈ ∂X` let `S(ω) = {j : ω ∈ D̂_j}`.
  - `S(ω) ≠ ∅`: `F` is the intersection of the near sides of its face planes, so an ultrafilter with `S = ∅` is
    principal.
  - `S(ω)` is a set of pairwise adjacent faces, since non-adjacent `D̂`'s are disjoint. So it is a face, an edge pair
    or a vertex triple.
- Put `f(ω) = s_i ω` with `i = min S(ω)`. The **pieces** `A_S = {ω : S(ω) = S}` are clopen.
- **Markov property.** `s_i` preserves `D̂_j` for `j` adjacent to `i`, and it maps `D̂_i` onto its complement. Every
  `D̂_k` with `k` non-adjacent to `i` misses `D̂_i`. Therefore
  `f(A_S) = ⋃ { A_T : i ∉ T, T ∩ adj(i) = S∖{i} }`, and `f|A_S = s_i` is injective.
- **Itineraries.** `ω ↦ (S(f^r ω))_r` maps `∂X` into the vertex shift `Σ` on pieces. The cylinder of a word `w` of
  length `n+1` is `[w] = u_w(A_{S_n})`, where `u_w = s_{i_0}⋯s_{i_{n−1}}`.

**Step 2 (directed geodesic rays; the coding is a homeomorphism).**
- **Lemma A carries over.** The tiles `τ_r(ω) = u_r F` form a geodesic ray. Each step crosses the face plane
  `u_rP_i`, which separates `τ_r` from `ω`, and no wall is recrossed. The ray converges to the Gromov image `ζ(ω) ∈ S²`
  of `ω`, because the far caps of far walls are small.
- **Lemma C carries over, with prisms for columns.**
  - Let `V` be a wall with `ζ ∈ ∂V`, or with the target on the far side of `V`. A tile on one side of `V`, not in
    `car(V)`, lies in a prism over a face `φ` of `V`'s induced right-angled tiling. The prism is bounded by the walls
    orthogonal to `V` through the edges of `φ`.
  - Inside the prism, the carrier tile `c_φ` is cut out by its face planes non-adjacent to `φ`. These are
    ultraparallel to `V`. So some wall disjoint from `V` separates the tile from `V`.
  - The height argument applies unchanged. Walls disjoint from `V` have circles missing `∂V`, so they are oriented by
    `ζ` or by the far side. So directed rays enter `car(V)`, and within `K_1` steps once they are `c_1`-close to it.
  - For the bound on time, the true geodesic to a point beyond `V` stays within its initial distance of `V` until it
    crosses `V`, because distance to a convex set is convex. The tile ray is Morse-close to that geodesic, and
    compactness bounds the region beyond each separating wall near `V`.
- **The itinerary map is injective.**
  - Ultrafilters with different `ζ` have different rays.
  - Two ultrafilters with the same `ζ` differ only on walls `V` with `ζ ∈ ∂V`. By Lemma C their common ray would enter
    `car(V)`, and there the piece state records the side of `V`.
- **It is continuous and onto.** Continuity is clear. For onto: an admissible word has nonempty cylinder
  `u_w(A_{S_n})`, and a decreasing intersection of nonempty compact sets is nonempty.
- So `∂X ≅ Σ`, `W`-equivariantly for the action of `W` on `∂X`. This is the analogue of the surface case's Step 4, and
  it is automatic here.

**Step 3 (irreducible core).**
- **Every piece reaches a central piece `C_x := A_{{x}}`.** Take `S` with `i = min S`:
  - `C_i → C_k` for every `k` non-adjacent to `i`;
  - an edge piece `A_{{i,j}}` goes to `C_j`;
  - a vertex piece `A_{{i,j,k}}` goes to `A_{{j,k}}`, and from there to a central piece.
  - These pieces are nonempty: the middle of the lens beyond an edge, the octant beyond a vertex, and the centre of a
    cap.
- **Central pieces reach each other along `𝒩`**, which is connected by (b).
- **A central piece reaches every piece.** `C_x → A_T` whenever `x ∉ T` and `T ∩ adj(x) = ∅`. By (a) such an `x`
  exists for every `T`, which lies at a vertex.
- So the piece graph is strongly connected. It is not a single cycle, since it branches (`C_i` has several successors).
- `Σ` has no isolated points.

**Step 4 (RSG and finite nucleus for `W`).**
- **RSG.** For cylinders `[w]`, `[w']` ending in the same piece, `u_{w'}u_w^{-1}` maps `[w] = u_w(A_S)` onto
  `[w'] = u_{w'}(A_S)`, preserving tails.
- **Finite nucleus.** Lemmas D and E of `closed-surface-groups-contracting-rsg-via-bowen-series` apply verbatim with
  walls in place of cut points:
  - **Lower bound.** Minimality of `[v] ⊇ h[w]` means two points of `h[w]` differ in the side of a face plane `W*` of
    the common tile `u_vF` or `u_v s F`. So `h^{-1}W*` splits `[w]`.
  - `h^{-1}W*` is not a face plane of any `τ_r`, `r ≤ n`, because the piece states fix those sides on `[w]`. So the
    `hF`-rays meet `car(W*)` only after time `n`, while the `F`-ray is in `car(W*)` by time `|v|+1`.
  - The quantitative Lemma C, with Lemma D, gives `|v| ≥ n + Δ − K_2`. When the `F`-ray's entry precedes the
    fellow-travel onset, there is a contradiction for `n ≥ n_0(h)`.
  - **Upper bound.** Two points of each piece have rays diverging within bounded time. Lemma D forbids a common prefix
    much longer than `n + Δ`.
  - **Conclusion.** `k = u_v^{-1}hu_w` has `d(F,kF) ≤ K`, uniformly in `h`.
- So `W` is a contracting RSG in `R_{Σ}`.

**Step 5 (finite-index subgroups: coset refinement).**
- Fix `Γ ≤ W` of finite index. The refined states are pairs `(A_S, c)` with `c ∈ Γ\W`, with an edge
  `(A_S, c) → (A_T, c·s_{min S})` whenever `A_T ⊆ f(A_S)`.
- Put `E` = the paths starting at states with `c = Γ`. Coordinates of the coset are determined by the piece word, so
  `E ≅ ∂X` `Γ`-equivariantly.
- **RSG.** If `[w]`, `[w']` end in the same refined state, then `Γu_w = Γu_{w'}`. So the canonical similarity
  `u_{w'}u_w^{-1}` lies in `Γ`.
- **Finite nucleus.** A local action of `h ∈ Γ` is determined by `k` (Step 4) and two cosets.
- **Irreducible core.** Let `G_loop` be the group generated by the labels of loops at a central piece `C_m`.
  - Along closed walks in `𝒩`: `m, k, m` gives `s_m s_k`, and `m, k, l, k, m` gives `s_m s_k s_l s_k`. So `s_l s_k` lies
    in `G_loop` for every edge of `𝒩`, and by (b) `G_loop` contains the even subgroup `W^+`.
  - An odd cycle of `𝒩` (c) gives an odd loop label, so `G_loop = W`.
  - Hence the loops at `C_m` act transitively on `Γ\W`. With Step 3, the refined graph is strongly connected.
- So `Γ` is a contracting RSG. Groups commensurable with `W` contain some such `Γ` with finite index, and
  `contracting-rsgs-closed-under-finite-index-overgroups` finishes item 3. ∎

**Dodecahedron check** (target, Statement): (a) 9 of the 12 faces are within one step of a vertex's three faces;
(b) `𝒩` is connected; (c) `𝒩` contains a triangle `m, r, r'`.

**For the referee.**
- The quantitative carrier lemma in 3D: the prism decomposition and the compactness bound.
- The injectivity of the coding on the fibres over points of wall circles, including intersection points of two
  orthogonal circles, where 4 ultrafilters lie over one point.
