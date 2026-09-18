---
rg: 2
id: two-graph-brick-codings-die-at-connected-corners
kind: claim
title: A finite 2-graph with rank-two H^1, one transport class per colour and connected corner compatibility graphs has no brick coding in any dimension
artifacts:
  - research/artifacts/nv-brick-coding-corner-kill-2026-09-17.md
distinct_from:
  two-graph-brick-codings-are-rigid-under-rank-two-h1: that proposition only constrains brick codings (power-of-two row sums, m at most log_2 of the row sums) and leaves the power-of-two case open; this adds the corner connectivity hypothesis (C1) and excludes brick codings outright, whatever the row sums.
  cmsz-pg22-rs-two-graphs-admit-no-brick-coding: that is a SAT-certified statement about five explicit graphs; this is an abstract theorem with no computation.
---

Let `Λ` be a finite 2-graph in which every vertex emits edges of both colours. Brick
codings (B1)–(B3) are as in `brick-coded-two-graph-full-groups-embed-in-brin-thompson`,
and (R1)–(R3) are as in `two-graph-brick-codings-are-rigid-under-rank-two-h1`.

For a vertex `a`, the **corner graph** `B_1(a)` is the bipartite graph on the colour-1
and colour-2 edges with source `a`. It joins `e` to `f'` iff some square `ef = f'e'`
exists.

**(C1)** `B_1(a)` is connected for every vertex `a`.

**Claim.** If `Λ` satisfies (R1), (R2), (R3) and (C1), then `Λ` has no brick coding in any
dimension `m ≥ 1`.

**Where every coding dies.**

- By (B2), `φ_j(e)` and `φ_j(f')` are prefixes of one word, so adjacent corner edges have
  comparable codes.
- By (C1), if all codes at `a` were nonempty in coordinate `j`, they would share a first
  letter. The colour-1 bricks at `a` would then miss half of `C^m`, contradicting (B1).
- So every vertex emits an edge with empty `j`-code. Following these edges gives a closed
  path `ξ` of degree `(p,s) ≠ 0` with `ℓ_j(ξ) = 0`.
- But by rigidity (b), `ℓ_j(ξ) = α_j p + β_j s > 0`. Contradiction.

Route: `two-graph-brick-codings-die-at-connected-corners-proof` (Theorem E of the artifact).
