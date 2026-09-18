---
rg: 2
id: rank-two-h1-tile-two-graphs-admit-no-brick-coding
kind: claim
title: Over every PG(2,q), a triangle-presentation tile 2-graph with irreducible colour matrices, rank-two H^1 and one transport class per colour admits no brick coding in any dimension
artifacts:
  - research/artifacts/nv-brick-coding-corner-kill-2026-09-17.md
distinct_from:
  cmsz-pg22-rs-two-graphs-admit-no-brick-coding: that covers five explicit q = 2 graphs via SAT; this covers every q and every presentation once the linear-algebra hypotheses hold, with no SAT.
  cmsz-pg23-rs-two-graphs-admit-no-brick-coding: that uses 9 not being a power of 2; this also covers q = 2^r, where the Kraft argument is silent.
  two-graph-brick-codings-die-at-connected-corners: that is the abstract theorem with (C1) as a hypothesis; this specializes to tile 2-graphs, where (C1) is proved.
---

Let `T` be a triangle presentation over `PG(2,q)` satisfying (A1)–(A3), and let `Λ_T` be
its tile 2-graph as in `triangle-presentation-tile-two-graphs-have-affine-corner-graphs`.
Assume:

- (H1) unique filling;
- (R1) `M_1` and `M_2` are irreducible (their row sums are automatically `q^2`);
- (R2) `dim_R H^1(K(Λ_T);R) = 2`;
- (R3) one transport class per colour.

**Claim.** `Λ_T` has no brick coding in any dimension `m ≥ 1`. So Theorem A of
`brick-coded-two-graph-full-groups-embed-in-brin-thompson` gives no embedding
`[[Λ_T]] ↪ mV` for any `m`.

The identification of `Λ_T` with the Robertson–Steger 2-graph of `Γ_T` is not part of this
claim.

This reduces the brick-coding branch of the negation route to finite linear algebra, for
every `q`. For `q = 2^r ≥ 4` no presentation had been tested before.

Route: `rank-two-h1-triangle-presentation-no-brick-coding-proof` (Corollary G of the
artifact).
