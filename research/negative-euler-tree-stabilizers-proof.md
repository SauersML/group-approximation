---
rg: 2
id: negative-euler-tree-stabilizers-proof
kind: route
title: Count edge ends; each edge group has Euler characteristic index times that of its vertex group, and the minimal subtree has no leaves
target: negative-euler-inputs-get-infinitely-generated-tree-stabilizers
requires:
  - bliw-locally-finite-tree-actions-embed-in-fp-simple-groups
---

Conventions:
- Trees are acted on without inversions. Otherwise pass to the barycentric subdivision. That keeps
  local finiteness, and it keeps vertex stabilizers virtually free: a midpoint stabilizer contains
  the pointwise stabilizer of the edge, a subgroup of a vertex stabilizer, with index at most 2.
- `χ` is the rational Euler characteristic. It is multiplicative on finite-index subgroups:
  `χ(K) = [L:K] χ(L)`. Also `χ(F_n) = 1 - n`.

## Step 1: item 1, the edge-end count

Let `𝒢` be the finite graph of groups, with Bass--Serre tree `T`. It is locally finite because the
edge inclusions have finite index.

**The formula.**
- `G` has a finite `K(G,1)`, built as a graph of finite graphs.
- So `χ(G) = Σ_[v] χ(G_v) - Σ_[e] χ(G_e)`, the second sum over geometric edge orbits.
- Each geometric edge `e` has two ends, at vertices `o(e)` and `t(e)`, possibly in the same orbit.
  Finite index gives `χ(G_e) = [G_{o(e)} : G_e] χ(G_{o(e)})`, and likewise at `t(e)`.
- So `Σ_[e] χ(G_e) = (1/2) Σ_[v] χ(G_v) Σ_{ends at [v]} [G_v : G_e]`.
- The inner sum equals `deg(v)`. The star of `v` in `T` splits into `G_v`-orbits, one for each edge
  end at `[v]` in the quotient graph, and the orbit of the edge through that end has
  `[G_v : G_e]` elements. There are no inversions, so the two ends of a loop give two distinct orbits.
- This yields `χ(G) = Σ_[v] χ(G_v)(1 - deg(v)/2)`.

**The sign.**
- `T` is `G`-minimal and not a point, so it has no leaves. If a vertex had valence at most 1,
  removing its orbit together with the incident edges would leave a smaller invariant subtree.
  Hence `deg(v) >= 2`.
- Every vertex group is free, so `χ(G_v) <= 0`.
- So every term is `>= 0`.

**Equality.** A term vanishes iff `G_v` is cyclic or `deg(v) = 2`.
- The vertex groups are pairwise commensurable, since each edge group has finite index in both of
  its vertex groups. So they are either all cyclic or all non-cyclic.
- If they are non-cyclic, equality forces every valence to be 2, so `T` is a line.

**BS classes.** A member of `BS_{F_2}` or `BS_Z` that is not free is either elliptic in its own
tree, in which case it is a vertex group and hence free (excluded), or it restricts to a minimal
subtree. That gives a reduced graph of groups of the same kind.

## Step 2: item 2, restriction to the input

Let `G <= H` be finitely generated, torsion-free and not free.

**Stabilizers.** Each `G_x = G ∩ H_x` is a torsion-free subgroup of a virtually free group, hence
free. Its intersection with a free finite-index subgroup of `H_x` is free and has finite index in
`G_x`, and a torsion-free virtually free group is free by Stallings.

**`G` is not elliptic.**
- If `G` fixed a vertex, it would be free.
- By Serre (*Trees*, I.6.5, Corollary 3), a finitely generated group all of whose elements are
  elliptic fixes a vertex. So `G` has a hyperbolic element.
- Hence `G` has a unique minimal invariant subtree `T_G`, the union of the axes of its hyperbolic
  elements.

**`T_G` is cocompact.**
- Pick a vertex `p ∈ T_G` and a finite generating set `S`.
- The union of the translates `g[p, sp]`, for `g ∈ G` and `s ∈ S`, is connected, because every
  `g p` is joined to `p` by a concatenation of such segments. It is `G`-invariant and has finitely
  many edge orbits.
- It contains `T_G`, so `T_G` has finitely many edge orbits too.

**Local finiteness and finite index.**
- `T_G` is locally finite, being a subtree of `X`.
- For an edge `e = [v, w]` of `T_G`, `G_e` is the stabilizer of `w` in `G_v`. The group `G_v`
  permutes the finitely many neighbours of `v`, so `[G_v : G_e] < ∞`.
- So `G = π_1` of a finite graph of free groups with finite-index edge inclusions and minimal
  Bass--Serre tree `T_G`.

**Finite generation spreads.**
- Adjacent vertex groups share a finite-index subgroup, so finite generation passes along edges,
  and hence to all of `T_G`.
- A vertex `x ∉ T_G` has a nearest point `q ∈ T_G`. Every `g ∈ G_x` preserves `T_G`, so it fixes
  `q`. Thus `G_x` is the stabilizer of `x` in `G_q`, which has finite index because `G_q` permutes
  the finitely many vertices at distance `d(x, q)` from `q`.
- So `G_x` is finitely generated iff `G_q` is.

**Conclusion.** If one `G_x` is finitely generated, all are, and `G` is as in item 1. The rational
Euler characteristic of `G` does not depend on which finite `K(G,1)` computes it, so `χ(G) >= 0`.

## Step 3: items 3 and 4

- **Item 3** is the contrapositive of item 2.
- **The HNN value.** For `G = F *_{φ : A -> B}`, the standard 2-complex, built from a graph for
  `F` and a cylinder on a graph for `A`, gives `χ(G) = χ(F) - χ(A) = a - r`. Here `G` is
  torsion-free and has a finite `K(G,1)`.
- **Freeness must be assumed.** It is not automatic. `< x, y, t | t x t^-1 = y >` is free of rank 2
  and has `χ = -1`. So the kill applies to every non-free `G` with `a < r`.
- **The surface example.** The genus-`g` surface group, for `g >= 2`, is an HNN extension of
  `F_{2g-1}` over `Z`. It has `a = 1` and `r = 2g - 1`, so `χ = 2 - 2g < 0`.
- **Item 4.** From the equality case, `T_G` is a line with finitely generated free, non-cyclic
  stabilizers.
  - Let `K` be the kernel of `G -> Aut(line) = D_∞`. It has index at most 2 in a vertex stabilizer,
    so it is finitely generated free.
  - The image is infinite because `G` is not elliptic, so it is `Z` or `D_∞`.

## Sanity checks

- **`F_n × Z`:** a loop edge with index 1, `χ = 0`, and `T` is a line.
- **`F_2 *_{F_3} F_2`:** index 2 on both sides, `χ = -1 - 1 + 2 = 0`. The valences are 2, so `T` is
  a line. The group is (free of rank 3)-by-`D_∞`, with `F_3` normal.
- **Vertices `F_2` and `F_3` with edge `F_5`:** indices 4 and 2, `χ = -1 - 2 + 4 = 1`. The formula
  gives `(-1)(1 - 4/2) + (-2)(1 - 2/2) = 1`, which agrees.
