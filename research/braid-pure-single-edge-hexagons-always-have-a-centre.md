---
rg: 2
id: braid-pure-single-edge-hexagons-always-have-a-centre
kind: claim
title: In the arc model of B_n, three x-arcs to a boundary point whose pairs have common spider neighbours on one puncture set have a common spider neighbour (Z/2 Helly number 2), so every pure single-edge A_{n-1} hexagon has a centre
distinct_from:
  h4-i25-shadow-centre-forms-hold-only-up-to-rotation: that states the A_3 pair lemma as open, with 1910 tests; this proves it in every rank, with a sharper Helly statement.
  h4-a2-fibred-shadows-are-a4-pure-braid-retractions: that identifies the A_2 shadows with A_4 single-edge hexagons; this proves that all such pure hexagons have centres.
---

**Model.**
- `D` is a closed disc with punctures `1,…,n` and two marked boundary points `d_0, d_1 ∈ ∂D`.
- `B_n = Mod(D, ∂D)`, with standard generators `σ_1,…,σ_{n-1}`.
- `x_0` is an arc from puncture `n` to `d_0`. Its stabiliser is `A_X = ⟨σ_1,…,σ_{n-2}⟩`.
- Fix `1 ≤ k ≤ n-2`. The *spider* `y_0` is `k` arcs (legs) from `d_1` to the punctures `1,…,k`. The legs are
  pairwise disjoint except at `d_1`. Its stabiliser is `A_Y = ⟨σ_{k+1},…,σ_{n-1}⟩`.
- The case `k = 1` is the `A_2`-shadow model `(X',Y')` of `h4-a2-fibred-shadows-are-a4-pure-braid-retractions`
  (`n = 5`) and the `A_3` model of w7-042 (`n = 4`).
- The case `k = 3`, `n = 7` is the `I_2(5)`-shadow model `(X'',Y'')` of
  `h4-i25-fibred-shadows-are-rigid-cluster-braid-groups`.

In the Deligne complex of `B_n` (type `A_{n-1}`):
- the vertices `gA_X` are the arcs `g x_0`;
- the vertices `hA_Y` are the spiders `h y_0`;
- `gA_X` and `hA_Y` are adjacent, meaning the cosets intersect, iff `g x_0` and `h y_0` have disjoint
  representatives (closures disjoint).

Here `d_0` sits next to `n` and `d_1` next to `1`, in the standard placement used by the cited nodes. The proof
checks this dictionary by cutting.

For a finite set `𝒳` of `x`-arcs in minimal position (for example hyperbolic geodesics), let `R(𝒳)` be the set of
punctures that lie in the complementary region of `⋃𝒳` adjacent to `∂D ∖ {d_0}`, excluding the endpoints of
the arcs in `𝒳`. This set does not depend on the minimal-position representatives.

**Theorem.**
1. **(Helly number 2.)** For `x`-arcs `x_1,…,x_m`,
   `R(x_1 ∪ ⋯ ∪ x_m) = ⋂_{i<j} R(x_i ∪ x_j)`.
   No common puncture is needed: every arc ends at `d_0`.
2. **(Centres.)** Three `x`-vertices `x_1,x_2,x_3` have a common spider neighbour iff
   `|R(x_1∪x_2) ∩ R(x_2∪x_3) ∩ R(x_3∪x_1)| ≥ k`.
3. **(Pure hexagons.)** Take a single-edge hexagon `x_1 y_{12} x_2 y_{23} x_3 y_{31}` in which the three spiders
   `y_{ij}` have the same leg set `P`, with `|P| = k`. This holds whenever the hexagon's letters are pure braids,
   and then `P = {1,…,k}`. Such a hexagon has a centre: a spider with legs to `P` that is adjacent to
   `x_1, x_2, x_3`.

For `k = 1, n = 4`, part 3 is the `A_3` pair lemma of `h4-i25-shadow-centre-forms-hold-only-up-to-rotation`.
That lemma was stated there as open.

**Idea of proof.**
- Suppose the union separates `p` from `∂D`. Then the boundary of `p`'s face is a mod-2 cycle `z` on the graph
  `⋃x_i`, and `z` has odd intersection with every path from `p` to `∂D`.
- Every arc passes through `d_0`. So each piece `z ∩ x_i` is a sum of "tails" `π_i(v)`, the subarc of `x_i` from
  `v` to `d_0`.
- The tails pair up at common vertices into cycles `π_i(v) + π_j(v) ⊂ x_i ∪ x_j`. One of these cycles has odd
  intersection with the path, so `x_i ∪ x_j` already separates.
- Realising all arcs as geodesics puts the pair neighbours and the triple in one picture.

The full proof is in `braid-pure-single-edge-hexagons-always-have-a-centre-proof`.

**Cross-check.** A combinatorial arc-placement test found 0 violations of part 1 in pure triples:
- `n = 4`: 1910 triples (w7-042's logs);
- `n = 5`: 3663 triples;
- `n = 6`: 4223 triples.

Files: `experiments/h4-pure-hexagon-z2-separation-2026-09-17/`.

**Status.** Established. The route `braid-pure-single-edge-hexagons-always-have-a-centre-proof` is a direct proof.
