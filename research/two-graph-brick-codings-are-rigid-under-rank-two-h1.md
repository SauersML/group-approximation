---
rg: 2
id: two-graph-brick-codings-are-rigid-under-rank-two-h1
kind: claim
title: If the square complex of a finite 2-graph has H^1 spanned by the degree cocycles, brick codings force power-of-two row sums and dimension at most log_2 of the row sums
artifacts:
  - research/artifacts/nv-brick-codings-of-two-graphs-2026-09-17.md
distinct_from:
  brick-coded-two-graph-full-groups-embed-in-brin-thompson: that shows a brick coding gives an embedding in mV; this constrains which 2-graphs can have a brick coding at all.
---

Let `Λ` be a finite 2-graph and `K(Λ)` its square complex. Its vertices are the vertices
of `Λ`, its edges are the edges of both colours, and it has one 2-cell per square
`ef = f'e'`. Let `d_i` be the colour-`i` indicator cochain. Brick codings (B1)–(B3) are
as in `brick-coded-two-graph-full-groups-embed-in-brin-thompson`. Assume:

- **(R1)** the colour matrices `M_1` and `M_2` are irreducible, with constant row sums
  `N_1` and `N_2`;
- **(R2)** `dim_R H^1(K(Λ); R) = 2`, so it is spanned by `[d_1]` and `[d_2]`;
- **(R3)** the colour-1 edges form one class under `e ~ e'` over squares `ef = f'e'`, and
  the colour-2 edges form one class under `f ~ f'`.

**Claim.** Let `φ` be a brick coding in dimension `m`. Then:

- (a) `N_1 = 2^α` and `N_2 = 2^β` with `α, β` integers. Every colour-1 edge has total
  code length `α`, and every colour-2 edge has total code length `β`.
- (b) In `H^1`, every coordinate length cocycle is `ℓ_j = α_j d_1 + β_j d_2` with
  `α_j, β_j > 0`, `Σα_j = α` and `Σβ_j = β`.
- (c) If `M_1` (resp. `M_2`) is primitive, every `α_j` (resp. `β_j`) is an integer, so
  `m ≤ α` (resp. `m ≤ β`).

In particular:

- Under (R1) and (R2) alone, a 2-graph whose `N_1` or `N_2` is not a power of 2 has no
  brick coding in any dimension.
- Under (R1)–(R3) with `N_1 = N_2 = 4` and primitive `M_i`, every brick coding has
  `m ≤ 2` and total length 2 on every edge.

For one-graphs the analogue is false: the prefix code `{0,10,11}` codes the three-loop
graph.

Route: `two-graph-brick-coding-rigidity-proof` (Proposition B of the artifact).
