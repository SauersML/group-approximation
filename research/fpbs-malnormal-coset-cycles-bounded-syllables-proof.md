---
rg: 2
id: fpbs-malnormal-coset-cycles-bounded-syllables-proof
kind: route
title: Pigeonhole on hull cocompactness, then cover each side of a tree polygon by the other sides
target: fpbs-malnormal-coset-cycles-bounded-syllables
requires: []
artifacts:
  - research/artifacts/fpbs-malnormal-coset-cycles-2026-09-17.md
---

A complete direct proof. It uses only the following:
- free groups act on their Cayley trees;
- a finitely generated subgroup has a finite based Stallings graph;
- in a tree, a closed edge path crosses every edge an even number of times.

**Setup.** `F` acts on the left on `T = Cay(F, S)`. The vertex set of `T` is
`F`, and `d(u, v) = |u^{-1} v|_S`. Let `Y` be the smallest subtree containing
`H`, which includes the vertex `e`. It is `H`-invariant. The quotient `H \ Y`
is the based Stallings graph of `H`, with `m` vertices. Fix representatives
`c_1, ..., c_m` of the `H`-orbits of vertices of `Y`. Every vertex of `Y` is
then `h c_r` for some `h in H` and some `r`. The hull of `gH` is `gY`.

**Item 1 (bounded overlap).** Suppose `gY ∩ g'Y` contains a geodesic with
vertices `v_0, ..., v_N`, where `N >= D = m^2`.
- **Pigeonhole.** Write `v_j = g h_j c_{r_j} = g' h'_j c_{r'_j}`. The pair
  `(r_j, r'_j)` takes at most `m^2` values, and there are `N + 1 > m^2`
  indices. So some `j < j'` have `r_j = r_{j'}` and `r'_j = r'_{j'}`.
- **One element in both conjugates.** Put
  `u = g h_{j'} h_j^{-1} g^{-1} in gHg^{-1}`. Then `u v_j = v_{j'}`. From the
  second expression we also get `u' = g' h'_{j'} h'_j{}^{-1} g'^{-1}` with
  `u' v_j = v_{j'}`. Here `v_j` and `v_{j'}` are both group elements. So
  `u = v_{j'} v_j^{-1} = u'`, which lies in `gHg^{-1} ∩ g'Hg'^{-1}`.
- **Contradiction.** `u != e` because `v_j != v_{j'}`. Conjugating by `g^{-1}`
  gives `H ∩ (g^{-1}g') H (g^{-1}g')^{-1} != 1`. By malnormality
  `g^{-1} g' in H`, so `gH = g'H`.

Hence distinct hulls meet in a subtree, since the intersection of subtrees is
connected, and every geodesic in that subtree has length `< D`.

**Item 2 (syllables).** Consider a simple cycle in the coset graph with `k`
`t`-edges. Its vertices are `g_0 H, ..., g_{k-1} H`, pairwise distinct, and
indices are taken mod `k`. Choose base points `p_0 = g_0` and move along the
cycle:
- the side `σ_i` is the geodesic in `T` from `p_i` to `q_i = p_i h_i`,
  with `h_i in H`;
- the short side `τ_i` is the geodesic from `q_i` to
  `p_{i+1} = q_i t^{ε_i}`;
- the equation `p_k = p_0` is the relation.

The facts used are these:
- Both ends of `σ_i` lie in `p_i H = g_i H`, so `σ_i ⊂ g_i Y`, and its length
  is `|h_i|_S`.
- Each `τ_i` has length `|t|_S`.
- The closed path `σ_0 τ_0 σ_1 τ_1 ... σ_{k-1} τ_{k-1}` crosses every edge of
  `T` an even number of times.

Take an edge `f` on `σ_i`. Since `σ_i` is a geodesic, it crosses `f` exactly
once, so another side crosses `f`. For `j != i`, the edges shared by `σ_i` and
`σ_j` lie in `g_i Y ∩ g_j Y`. This is a subtree, and `σ_i` is a geodesic, so
the shared edges form one subsegment of length `< D`, by Item 1 and
`g_i H != g_j H`. Each `τ_j` shares at most `|t|_S` edges with `σ_i`. Summing
over the other sides gives

    |h_i|_S = length(σ_i) <= (k-1)(D-1) + k |t|_S.

**Item 3 (finiteness).** A simple cycle through a fixed edge `e(g)` with
`k <= R+1` `t`-edges is determined by three pieces of data:
- the signs `ε_i`;
- the syllables `h_i`, each an element of `H` of bounded `S`-length, so there
  are finitely many;
- the position of `e(g)` on the cycle.

So there are finitely many such cycles. Every detour for `e(g)` contains a
simple path from `gH` to `gtH` that avoids `e(g)`. Adding `e(g)` gives a simple
cycle with one more `t`-edge. Edge-disjoint detours contain edge-disjoint
simple paths, which give distinct cycles. Hence each packing has only finitely
many detours with at most `R` `t`-edges.
