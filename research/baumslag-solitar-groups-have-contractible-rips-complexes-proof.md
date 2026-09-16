---
rg: 2
id: baumslag-solitar-groups-have-contractible-rips-complexes-proof
kind: route
title: Triangulate the aspherical one-relator complex along a staircase and match triangles with Cayley 3-cliques by t-exponent bookkeeping
target: baumslag-solitar-groups-have-contractible-rips-complexes
requires:
  - group-rips-complexes-are-cayley-graph-flag-complexes
artifacts:
  - research/artifacts/baumslag-solitar-contractible-rips-2026-09-16.md
---

The full proof is in the artifact. Outline, with `φ : G -> Z` the
`t`-exponent map:

1. **Contractible cover.** Let `X~` be the universal cover of the presentation
   complex. It is simply connected and 2-dimensional.
   - The relator cell `D_g` crosses the `t`-edges `(g,t)` and `(g a^n,t)` with
     opposite signs and no other `t`-edge.
   - So a 2-cycle `Σ c_g D_g` has `c` constant on the infinite cosets
     `x<a^n>`. Since `c` has finite support, `c = 0`.
   - Hence `H_2(X~) = 0`, and `X~` is contractible by Hurewicz–Whitehead.

   Each relator 2-cell `D_g` is a polygon with pairwise distinct boundary
   vertices:
   - top: `g t a^r`, `0 <= r <= m`;
   - bottom: `g a^(δi)`, `0 <= i <= N`.

   Cutting every `D_g` along the chords `g a^(δi) — g t a^r`, `(r,i) ∈ P`,
   gives a contractible 2-complex `Y`. The chord at `(r,i)` has label
   `s(r,i) = a^(-δi) t a^r`.
2. **Labels.** By Britton's lemma, `s(p) = s(p')` iff `p - p' ∈ Z(m,N)`. So
   `s` identifies only the endpoints of `P`, and `|S| = 2 + 2(m+N)`.
3. **1-skeleton.** The edges of `Y` have pairwise distinct endpoint pairs, and
   these pairs are exactly the edges of `Cay(G,S)`. Pairs with equal `φ` are
   `a`-edges; the others are determined by their label via step 2.
4. **Cliques are triangles.**
   - In a 3-clique the `φ`-increments lie in `{-1,0,1}` and sum to `0`. Since
     `a` has infinite order, the clique has exactly one `a`-edge `{g, ga}`,
     and its third vertex `k` has `φ(k) - φ(g) = ±1`.
   - The two labels from `{g, ga}` to `k` are `u` and `ua`, or `u` and
     `a^-1 u`, with `u ∈ T`. They lie on the periodic path
     `P^ = P + Z(m,N)` at points differing by `(1,0)` or `(0,±1)`.
   - Such points are consecutive on the monotone path `P^`. Hence
     `{g, ga, k}` is a triangle of some `D_(g_0)`.
5. **Flagness.** `Y` is 2-dimensional and contractible, so
   `H_2(Y;F_2) = ker ∂_2 = 0`. Two triangles on the same vertex set would give
   a nonzero 2-cycle, and so would the four triangles of a 4-clique.
   - Hence `Y` is a simplicial complex whose triangles are exactly the
     3-cliques, and `Cay(G,S)` has no 4-cliques.
   - So `Flag(Cay(G,S)) = Y` is contractible.
   - By item 1 of `group-rips-complexes-are-cayley-graph-flag-complexes`, it
     equals `R_1(G,S)`.

Britton's lemma and the embedding of the base group of an HNN extension are
used as standard background (Lyndon–Schupp, Ch. IV). A brute-force check of
steps 2–5 is in
`experiments/baumslag-solitar-contractible-rips-2026-09-16/check_bs_rips.py`.
It covers `1 <= m <= 4`, `1 <= |n| <= 4` and all staircase paths, 484
generating sets, and exits `0`. A referee script written independently,
`referee_check_bs.py` in the same directory, checks the vertex-`1` predictions
for 329 further generating sets. These come from twelve groups up to
`BS(8,5)` and `BS(6,-9)`: `|S|`, `3(m+N)` triangles at `1`, and no 4-clique.
The proof does not use either computation.
