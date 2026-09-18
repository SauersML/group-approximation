---
rg: 2
id: two-graph-brick-codings-die-at-connected-corners-proof
kind: route
title: Square comparability propagates one first letter across a connected corner, forcing a zero-length cycle against positive slopes
target: two-graph-brick-codings-die-at-connected-corners
requires:
  - two-graph-brick-codings-are-rigid-under-rank-two-h1
artifacts:
  - research/artifacts/nv-brick-coding-corner-kill-2026-09-17.md
---

Full proof: Part E (Theorem E, Steps E1–E4) of the artifact. Let `φ` be a brick coding,
and fix a coordinate `j`.

1. **E1.** On a square `ef = f'e'`, the words `φ_j(e)` and `φ_j(f')` are both prefixes of
   `φ_j(e)φ_j(f) = φ_j(f')φ_j(e')`. So they are comparable, and when both are nonempty
   they share their first letter.
2. **E2.** Suppose every edge at `a` has a nonempty `j`-code. By (C1), all these codes
   begin with one letter `c`. Then the colour-1 bricks at `a` lie in `{x_j ∈ cC}`, which
   contradicts (B1). So each vertex `a` emits an edge `σ(a)` with empty `j`-code.
3. **E3.** Iterating `σ` on the finite vertex set gives a closed edge path `ξ` of degree
   `(p,s)` with `p + s ≥ 1` and `ℓ_j(ξ) = 0`.
4. **E4.** Imported verbatim from part (b) of
   `two-graph-brick-codings-are-rigid-under-rank-two-h1` (ESTABLISHED), under (R1)–(R3):
   "In `H^1`, every coordinate length cocycle is `ℓ_j = α_j d_1 + β_j d_2` with
   `α_j, β_j > 0`".
   - Coboundaries vanish on closed paths, so `0 = ℓ_j(ξ) = α_j p + β_j s > 0`.
   - This is a contradiction.
