---
rg: 2
id: nonbacktracking-walks-on-regular-multigraphs-return-rarely
kind: claim
title: A nonbacktracking walk on a connected d-regular multigraph with more than two vertices returns with probability at most (d-2)/(d-1)
distinct_from:
  density-random-groups-no-finite-quotients-below-exp-k: that bounds, by a letter swap, the probability that a uniform cyclically reduced word lies in a kernel by 1 − κ_m; this bounds the return probability of a nonbacktracking walk, which covers uniform reduced words, by (2m-2)/(2m-1)
artifacts:
  - research/artifacts/solve-hyperbolic-rf-simple-quotients-2026-09-13.md
---

**ESTABLISHED** by literature import `nonbacktracking-walk-return-bound-citation`.

**THEOREM** (Kozma–Lubotzky, arXiv:1810.01529, Lemma `lem:half`). Let `G` be a connected
`d`-regular multigraph with `d >= 4` and more than 2 vertices, `x` a vertex, and `t > 1`.
If `N(t)` is a nonbacktracking random walk started at `x`, then

```text
P^x( N(t) = x ) <= (d − 2)/(d − 1).
```

**Conventions (source).**
- Multigraphs may have multiple edges and self-loops, and a self-loop counts twice toward
  the degree.
- The walk never traverses an edge and then the same edge backwards. A self-loop may be
  traversed in either direction.
- The first step is unrestricted. Each later step picks uniformly among the `d − 1`
  allowed continuations.

**Use for words.** Let `φ: F_m -> Q` be a homomorphism and `A_i = φ(x_i)`. Take the
Cayley multigraph of `φ(F_m)` with respect to `A_1, …, A_m`:
- one edge from `g` to `gA_i` for each vertex `g` and each `i`;
- traversed forwards it multiplies by `A_i`, backwards by `A_i^{-1}`;
- a self-loop when `A_i = 1`.

This multigraph is `2m`-regular and connected. A uniform reduced word `ω` of length `l`,
read from vertex 1, is exactly a nonbacktracking walk: forbidding the inverse of the
previous letter is forbidding the reverse traversal of the edge just used. Its endpoint is
`φ(ω)`. So if `m >= 2`, `l >= 2` and `|φ(F_m)| > 2`, then
`P[φ(ω) = 1] <= (2m − 2)/(2m − 1)`. The source uses the lemma this way (l.593–604).
