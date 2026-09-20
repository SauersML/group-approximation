---
rg: 2
id: quasiconvex-in-hyperbolic-racgs-iff-square-free-typing-proof
kind: route
title: Develop a typed cube complex into the Davis complex by reading types along edge paths; restrict the Davis typing to a convex core for the converse; Helly for tight quadrilaterals
target: quasiconvex-in-hyperbolic-racgs-iff-square-free-typing
requires: []
---

**Lane proof** (lane `bh-q11-bridge`, 2026-09-19), elementary, **not independently reviewed**. Notation as in the claim.
Recalled standard inputs, not re-read at source:
- **(Mou)** Moussong: `W(Δ)` is hyperbolic iff `Δ` has no induced 4-cycle.
- **(LI)** A local isometry of CAT(0) cube complexes (a cubical map injective on links, with full image) is injective
  with convex image (Haglund–Wise, GAFA 2008, §2).
- **(Core)** A quasiconvex subgroup of a hyperbolic group acting geometrically on a CAT(0) cube complex acts
  cocompactly on some convex subcomplex (Haglund, Geom. Dedicata 2008, for RACGs; Sageev–Wise, PAMS 2015).
- **(Helly)** Pairwise intersecting convex subcomplexes of a CAT(0) cube complex have a common vertex.
- **(CAT0-special)** In a CAT(0) cube complex, the edges at a vertex are dual to distinct hyperplanes, and two of them
  span a square iff their hyperplanes cross.

## Item 1, (ii) ⇒ (i): the developing map

- **Definition.** Fix a vertex `y_0`. For a vertex `y`, choose an edge path from `y_0` to `y`. If its edges have types
  `s_1, …, s_k`, put `D(y) = s_1 ⋯ s_k ∈ W(Δ)`.
- **Well defined.** Two edge paths with the same ends differ by backtracks and square moves, since `Y` is simply connected
  and its 2-cells are squares.
  - A backtrack `e e⁻¹` contributes `s s = 1`.
  - A square move replaces `s t` by `t s`, where `s, t` are the types of two adjacent sides of a square. The two dual
    hyperplanes cross, so `s ~ t` by (T2), and `st = ts` in `W(Δ)`.
- **Cubical.** An edge of type `s` from `y` goes to the edge `{D(y), D(y)s}`. A cube at `y` whose edges have type set `T`
  (a clique, by (T2) and flagness) goes to the cube `D(y)W_T`.
- **Local isometry.** At `y`, the link map is injective by (T1), and its image is full by (T2) and flagness of both
  links. By (LI), `D` is injective and `D(Y)` is a convex subcomplex.
- **Equivariance.** Put `ρ(g) = D(g y_0)`. A path from `y_0` to `gy` can be taken to be a path from `y_0` to `gy_0`
  followed by the `g`-translate of a path from `y_0` to `y`, which has the same types because `τ` is `G`-invariant. So
  `D(gy) = ρ(g) D(y)`, and `ρ` is a homomorphism.
- **Injective.** If `ρ(g) = 1` then `D(gy_0) = D(y_0)`, so `gy_0 = y_0`, so `g = 1`, since `G` acts freely on vertices.
- **Quasiconvex.** `ρ(G)` acts cocompactly on the convex subcomplex `D(Y)`. So the orbit map
  `g ↦ ρ(g) = D(gy_0)` is a quasi-isometric embedding into the vertex set `W(Δ)` of `Σ(Δ)`, with its word metric. So
  `ρ(G)` is quasiconvex, and `W(Δ)` is hyperbolic by (Mou). ∎

## Item 1, (i) ⇒ (ii): restrict the Davis typing

- **Core.** Let `G ≤ W(Δ)` be quasiconvex, with `Δ` square-free. By (Core), `G` acts cocompactly on a convex subcomplex
  `Y ⊆ Σ(Δ)`. The action is proper, and free on vertices, since `W(Δ)` acts on its own vertex set by left
  multiplication.
- **Typing.** The hyperplanes of `Y` are the ambient hyperplanes that meet `Y`, taken injectively. Give each one its
  ambient type. Left multiplication preserves types, so the typing is `G`-invariant.
- **(T1) and (T2).** `Y` is convex, so each link `lk_Y(y)` is a full subcomplex of `lk_Σ(y) ≅ L(Δ)`, and the
  identification is by types. ∎

## Item 2

By (T1), (T2) and flagness, `lk(y)` is isomorphic to a full subcomplex of `L(Δ)`. The 1-skeleton of `L(Δ)` is `Δ`,
which has no induced 4-cycle, and full subgraphs of such graphs have none either. ∎

## Item 3

- **(⇐) Tight quadrilateral gives a square link.**
  - The carriers pairwise intersect: `N(H_i) ∩ N(H_{i+1}) ≠ ∅` since the hyperplanes cross, and the two diagonal pairs by
    hypothesis. By (Helly) they share a vertex `u`.
  - Each `u ∈ N(H_i)` is the vertex of a cube meeting `H_i`, which has an edge `e_i` at `u` dual to `H_i`.
  - By (CAT0-special), `e_i` and `e_{i+1}` span a square, while `e_1, e_3` and `e_2, e_4` do not, since those hyperplanes
    are disjoint. So `e_1 e_2 e_3 e_4` is an induced 4-cycle in `lk(u)`.
- **(⇒)** The four hyperplanes dual to the edges of an induced 4-cycle in `lk(u)` form a tight quadrilateral, with
  `u` in all four carriers. ∎
- **Why this matters.**
  - The identity map on hyperplanes is a typing into the crossing graph `Γ(Y)`, by (CAT0-special).
  - An induced square `H_1…H_4` of `Γ(Y)` can be killed by (M1) exactly when a diagonal pair does not co-occur.
  - Hyperplanes co-occur iff their carriers meet, so a square both of whose diagonals co-occur is a tight quadrilateral,
    and item 3 puts it at a single vertex link.

## Item 4

- **(M1).** (T1) does not involve adjacency. For (T2), no vertex carries both an `a`-edge and a `b`-edge, so adding the
  edge `ab` changes the adjacency of no pair of types present at a common vertex. ∎
- **(M2).**
  - (T1) holds after merging because `a` and `b` never co-occur.
  - For (T2) at a vertex `y`, the only pairs whose adjacency changes are an `a`-edge (or `b`-edge) together with a
    `c`-edge, where `c` is adjacent to `b` but not to `a` (or the reverse).
  - Such a `c` co-occurs with `a` at `y` and is non-adjacent to it, i.e. osculates `a`. The hypothesis excludes it.
  - `a ≁ b` guarantees the merged graph has no loop. ∎
- **Adding vertices.** Whether a 4-cycle is induced depends only on its four vertices, so new vertices kill no square.
  Any `Δ' ⊇ Δ` that keeps `τ` a typing agrees with `Δ` on co-occurring pairs, by (T2). So the only changes available are
  new edges between never-co-occurring pairs, which is (M1), and identifications of never-co-occurring types, which is
  (M2).

## Item 5

- **C-special gives a typing.** Let `X = Y/G` be C-special and type each hyperplane of `Y` by its image in `X`.
  - (T1): two edges at `y` with the same image would be a self-crossing or a self-osculation in `X`.
  - (T2): two edges at `y` whose images cross somewhere but do not span a square at `y` would be an inter-osculation.
  - So `Γ(X)` is a valid target, and the developing map of item 1 is the Haglund–Wise embedding into `W(Γ(X))`.
- **Every typing factors through it.** A `G`-invariant typing is constant on `G`-orbits of hyperplanes, i.e. on
  `Hyp(X)`. So it is `φ ∘ τ_HW`, and (T1) and (T2) for `τ` say exactly that `φ` is a full embedding on every link.
- **Covers help and never hurt.** Pulling a typing back to a finite cover keeps it valid, so passing to `X'` only enlarges
  the set of available `φ`.
- **Davis–Januszkiewicz.** If `Γ` has an edge then `A(Γ) ⊇ Z²`, and a group with a finite-index subgroup containing `Z²`
  is not hyperbolic. ∎

## For the referee

- Item 1 needs the action to be free on **vertices** only, not free. Groups with torsion are allowed, and reflections in
  `G` fix edge midpoints.
- Please check that (LI) is being applied in the right generality: `Y` is locally finite but possibly of unbounded
  dimension a priori. It is finite-dimensional here, since `Y` is cocompact.
- Items 3–5 are new organization, not new mathematics. The claim's value is item 5's reduction of the bridge to (B\*),
  plus item 2 as a necessary test.
