---
rg: 2
id: row29-magnus-overgroups-via-stallings-quotients
kind: route
target: row29-magnus-subgroups-have-no-intermediate-rank-two-overgroups
requires: []
artifacts:
  - research/artifacts/one-relator-magnus-row29-2026-09-13.md
  - research/artifacts/one-relator-magnus-row29-scripts/algext.py
  - research/artifacts/one-relator-magnus-row29-scripts/algext.out
---

**Proof.**

*Step 1 (the core graphs).* Write `X = x^(-1)`, `Y = y^(-1)`, so `v = XyyXXY`.
Folding the petals `x` and `v` at a base vertex gives the core graph `Gamma_-` of
`F_-` with 4 vertices and 5 edges: `x : 0 -> 0`, `y : 0 -> 1`, `y : 1 -> 2`,
`x : 1 -> 3`, `x : 3 -> 2`. Its rank is `5 - 4 + 1 = 2`. Vertex 2 has no outgoing
`y`-edge, so `Gamma_-` is not a covering of the rose and `F_-` has infinite index.
Folding `v` and `y` gives `Gamma_+` with 5 vertices and 6 edges, rank 2, again not a
covering. `algext.out` records both counts.

*Step 2 (rank-two overgroups are folded quotients).* Let `H <= K <= F` be finitely
generated with `rank H = 2` and `rank K <= 2`. The inclusion induces a pointed
immersion `iota : Gamma_H -> Gamma_K` between pointed core graphs (Stallings). Let
`Q = iota(Gamma_H)`. It is connected, contains the base vertex, and is folded because
`Gamma_K` is. Since `pi_1 Q` contains the nonabelian group `H`, `rank Q >= 2`.

Let `E'` and `V'` be the edges and vertices of `Gamma_K` not in `Q`. Then
`rank Gamma_K - rank Q = |E'| - |V'|`. The base vertex lies in `Q`, so every vertex in
`V'` has degree at least 2 in `Gamma_K`, and every edge at such a vertex lies in `E'`.
Counting endpoints gives `2|V'| <= 2|E'|`. Equality forces every edge of `E'` to have
both endpoints in `V'`. Then `E' u V'` is a union of components disjoint from `Q`,
which is impossible in a connected graph unless `E'` is empty. So if `E'` is nonempty,
`rank K >= rank Q + 1 >= 3`. Hence `rank K <= 2` forces `Gamma_K = Q` and
`K = pi_1 Q`.

*Step 3 (enumeration).* `Q` is the quotient of `Gamma_H` by the vertex fibres of
`iota`, with the resulting parallel edges identified, and it is already folded. So `Q`
arises by choosing a set partition of `V(Gamma_H)`, identifying each block, and
folding. `algext.py` does exactly this for every partition. It canonicalizes the
pointed result by breadth-first relabelling from the base vertex and reports each
folded quotient of rank 2 that differs from `Gamma_H`. The partitions number 15 for
`Gamma_-` and 52 for `Gamma_+`.

*Step 4 (result).* In both cases the only folded quotient of rank at most 2, other
than `Gamma_H` itself, is the one-vertex rose with loops `x` and `y`, whose `pi_1` is
`F`. By Step 2, a rank-two `K` containing `F_-` (or `F_+`) is `F_-` (or `F_+`)
or `F`.

*Calibration.* On `H = <x^2, y^2>` the same script reports the rank-two overgroups
`<x, y^2>`, `<x^2, y>` and `F`, which are the expected ones.

*Consequence for cyclic splittings.* A graph of free groups with infinite cyclic edge
groups has Euler characteristic equal to the sum of the vertex characteristics. For
`F = A *_Z B` this is `-1 = (1 - r_A) + (1 - r_B)` with `r_B >= 1`, so `r_A <= 2`.
For `F = A *_Z` it is `-1 = 1 - r_A`, so `r_A = 2`. Vertex groups of a nontrivial
splitting are proper subgroups. So by Step 4 a vertex group containing `F_-` or `F_+`
equals it.
