---
rg: 2
id: c2-mapping-torus-realizations-are-free-factor-level-splits-proof
kind: route
title: The midline graph of a 2-cell-injective map into M_f is an edge-injective immersion into Gamma. It cuts K into a graph of spaces whose vertex groups lie in N and whose edge groups form a free factor system. Conversely, an FFLS is assembled over the rose adapted to its free factor system. The level rewriting of the one-relator (C2) group gives width 3 with non-free-factor edge groups
target: c2-mapping-torus-realizations-are-free-factor-level-splits
requires:
  - two-cell-injective-maps-realize-relative-eg-pairs
  - c2-fibred-realizations-reduce-to-a-primitive-class
  - c2-split-rose-passes-cycle-test-fails-gluing-rank
artifacts:
  - experiments/c2-level-splitting-2026-09-17/RESULTS.md
  - experiments/c2-level-splitting-2026-09-17/hlib.py
  - experiments/c2-level-splitting-2026-09-17/ff.py
  - experiments/c2-level-splitting-2026-09-17/fftest.py
---

The notation is that of the target.

## Necessity

Let `F: K → M_f` be combinatorial and 2-cell-injective, with `K` a finite 2-dim `K(H,1)` and
`F_* : π_1 K ≅ H ≤ G`. `F` is combinatorial: it sends each open cell homeomorphically onto an open
cell, and distinct 1-cells may have the same image. The 1-cells of `K` sent to vertical 1-cells are
called vertical; the others are horizontal.

- **Every 2-cell of `K` has the shape of `σ_e`.** A 2-cell `κ` maps onto some `σ_e`, and its boundary
  maps cell by cell onto `∂σ_e`. So `∂κ` reads `ẽ · v_1 · P · v_2⁻¹`, where:
  - `ẽ` is one horizontal 1-cell over `e`;
  - `v_1, v_2` are vertical 1-cells;
  - `P` is a horizontal path over `f(e)`.
- **Midline graph `Λ`.**
  - Vertices of `Λ`: the midpoints of the vertical 1-cells of `K`.
  - Edges of `Λ`: the midline arcs of the 2-cells, each joining the midpoints of `v_1` and `v_2`.
  - Label each edge of `Λ` by the `e` of its cell. This gives `λ: Λ → Γ`, which is injective on edges
    because `F` is injective on 2-cells.
  - An edge-injective graph map is an immersion. Hence `λ` is `π_1`-injective on each component `Λ_j`.
- **Graph of spaces.**
  - Let `K_h` be the horizontal subcomplex, and let `X_v` be its components.
  - A regular neighbourhood of `Λ` in `K` is `Λ × [0,1]`. Its bottom `ι_0` pushes each midline arc
    onto its `ẽ`-side. Its top `ι_1` pushes it onto its `P`-side.
  - `K` deformation-retracts onto the graph of spaces with vertex spaces `X_v` and edge spaces `Λ_j`.
  - `ι_0` composed with `X_v → Γ` is `λ`, so `ι_0` is `π_1`-injective.
  - `ι_1` composed with the map to `Γ` is homotopic to `f ∘ λ`. That is `π_1`-injective because `f` is a
    homotopy equivalence. Hence `ι_1` is `π_1`-injective.
  - So `π_1 K = π_1 𝔾` for the graph of groups `𝔾` with vertex groups `V_v = π_1 X_v` and edge groups
    `E_j = π_1 Λ_j`.
- **The FFLS conditions.**
  - Horizontal loops map into `Γ`. So `F_*(V_v) ≤ F_n ∩ H = N`, and each `V_v` is f.g. because `X_v` is
    finite.
  - The stable letter of edge `j` crosses exactly one vertical 1-cell once, so `ε(t_j) = ±1`. Orient
    the edges of `Δ` so that `ε(t_j) = 1`.
  - `F_*` is injective with image `H`.
- **Free factor system.** Let `Y = λ(Λ) ⊂ Γ`.
  - `λ` is a bijection from the edges of `Λ` onto the edges of `Y`. So `Y` is obtained from `⊔ Λ_j` by
    identifying vertices only.
  - Hence `π_1 Y = ∗_j π_1(Λ_j)^{g_j} ∗ F_m`, where `F_m` comes from the identifications.
  - `π_1 Y` is a free factor of `π_1 Γ` because `Y` is a subgraph.
  - So `{λ_* E_j}` is a free factor system of `F_n` up to conjugacy.
  - Vertical 1-cells lying in no 2-cell give trivial edge groups.

This proves (A5): the class `c_H`, pushed into `F_n`, is carried by `π_1 Y`. It also proves (A4) for a rose.

## Sufficiency

Let `𝔾` be an FFLS.
- **The rose.** Choose `g_j ∈ F_n` and a basis `𝔅` of `F_n` such that `g_j E_j g_j⁻¹ = ⟨𝔅_j⟩`, with
  the `𝔅_j ⊂ 𝔅` pairwise disjoint. Let `ρ` be the rose on `𝔅` and `f_ρ` the rose map of `φ`.
- **Vertex spaces.** Write `t_j = h_j y` with `h_j ∈ F_n`. Let `X_v` be a finite connected subgraph of
  the cover `ρ̂_v → ρ` belonging to `V_v` that contains:
  - the core of `ρ̂_v`;
  - for each `j` with `ι j = v`, the vertex `u_j` at the end of the path `g_j⁻¹` from the basepoint.
    The loops at `u_j` labelled by `𝔅_j` close up, since `g_j⁻¹ 𝔅_j g_j ⊂ E_j ≤ V_v`;
  - for each `j` with `τ j = v`, the vertex `w_j` at the end of the path `h_j φ(g_j)⁻¹`, and the closed
    paths `φ(x)`, `x ∈ 𝔅_j`, at `w_j`. These close since `t_j E_j t_j⁻¹ ≤ V_v`.
- **Edge spaces and 2-cells.** For each `j`, attach one vertical 1-cell from `u_j` to `w_j`, over the
  vertical 1-cell of `M_{f_ρ}`. For each `x ∈ 𝔅_j`, attach one 2-cell along the loop `x` at `u_j`, the
  vertical 1-cell, and `φ(x)` at `w_j`, mapped onto `σ_x`.
- **Why this works.**
  - Distinct `j` use disjoint `𝔅_j`, so the map is 2-cell-injective.
  - `K` is the graph of spaces of `𝔾`, with the rose `R_{𝔅_j}` as its `j`-th edge space.
  - The bottom attaching map of each edge space is an immersion. The top is `φ` restricted to `⟨𝔅_j⟩`
    followed by a cover. Both are `π_1`-injective, so `K` is aspherical with `π_1 K = π_1 𝔾`.
  - The upward vertical 1-cell represents `y⁻¹`, since `σ_x` reads `x · y⁻¹ = y⁻¹ · φ(x)`.
  - So the path from the `ι j` basepoint to the `τ j` basepoint through edge `j` reads
    `g_j⁻¹ · y⁻¹ · φ(g_j) h_j⁻¹ = y⁻¹ h_j⁻¹ = t_j⁻¹`, as Bass–Serre requires.
  - The loop `φ(x)` at `w_j` reads `h_j φ(g_j⁻¹ x g_j) h_j⁻¹ = t_j (g_j⁻¹ x g_j) t_j⁻¹`.
  - So `π_1 K → G` is the morphism of `𝔾`: injective with image `H`.
