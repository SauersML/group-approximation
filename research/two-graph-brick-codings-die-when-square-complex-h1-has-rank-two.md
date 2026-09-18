---
rg: 2
id: two-graph-brick-codings-die-when-square-complex-h1-has-rank-two
kind: claim
title: A finite 2-graph without sources with rho(M_1) > 1 whose square complex, or that of a block recoding, has H^1 of dimension 2 admits no brick coding in any dimension
artifacts:
  - research/artifacts/nv-bernoulli-conformal-class-kill-2026-09-17.md
distinct_from:
  two-graph-brick-codings-are-rigid-under-rank-two-h1: that derives power-of-two row sums and a dimension bound from rank-two H^1 via Lebesgue measure and Kraft, so for row sums that are powers of 2 it still needs a SAT search; this shows rank-two H^1 alone rules out every brick coding, with no condition on row sums and no search.
  cmsz-pg22-rs-two-graphs-admit-no-brick-coding: that is a statement about five explicit q = 2 presentations proved by SAT; this is a general criterion that re-proves it from the rank-two H^1 certificate.
---

Brick codings (B1)–(B3) are defined as in `brick-coded-two-graph-full-groups-embed-in-brin-thompson`.
`K(Λ)` is the square complex: vertices, edges of both colours, and one 2-cell per square.
The higher-block 2-graph `Λ^{[k]}` is built from the rectangles of `Λ`:
- its vertices are the rectangles of degree `(k,k)`;
- its colour-`j` edges are the rectangles of degree `(k,k) + e_j`;
- its squares are the rectangles of degree `(k+1,k+1)`.

**Claim.** Let `Λ` be a finite 2-graph without sources, with `ρ(M_1) > 1`.
- (a) If `dim_R H^1(K(Λ); R) = 2`, then `Λ` has no brick coding in any dimension `m`, for
  any row sums.
- (b) If `dim_R H^1(K(Λ^{[k]}); R) = 2` for some `k ≥ 0`, then `Λ^{[k]}` has no brick
  coding in any dimension.

Route: `brick-coding-death-via-bernoulli-conformal-classes`.
