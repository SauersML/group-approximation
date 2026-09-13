---
rg: 2
id: thompson-f-is-sofic
kind: claim
title: Thompson's group F is sofic
refuted_by:
  - thompson-f-is-not-sofic
distinct_from:
  thompson-f-is-amenable: that is amenability, which implies this claim; a nonamenable F could still be sofic.
  thompson-v-is-sofic: that is soficity of V, which implies this claim because F <= V; the converse is not known.
---

**OPEN.** Thompson's group `F` embeds in the universal sofic group.

**Equivalent forms** (`thompson-f-sofic-iff-relator-system-unstable`):
- some almost-homomorphism of `F` has a fixed-point character with a regular component;
- there are `epsilon > 0` and permutation pairs `(A_n, B_n)` that satisfy both relators of `F` up to
  `delta_n -> 0` in normalized Hamming distance while `d(A_n B_n, B_n A_n) >= epsilon`.

Exact solutions commute, since finite quotients of `F` are abelian. So the second form must exploit the
error.

## Attempts

- Through `thompson-f-sofic-from-amenability` (waits on `thompson-f-is-amenable`) and `thompson-f-sofic-from-v-sofic` (waits on `thompson-v-is-sofic`). The equivalent almost-commuting form is in `research/artifacts/thompson-f-soficity-as-relator-stability-2026-09-12.md`, section 3.
- **Local embeddability into amenable groups collapses (2026-09-13).** `F` is finitely presented and every proper
  quotient is abelian, so a local embedding of a ball containing both relators and `[a,b]` into an amenable group
  is an injective homomorphism. So `F` is LEA only if amenable (`thompson-f-is-lea-only-if-amenable`), and LEA is
  not an independent soficity route.
- **Spatial permutation models almost commute (2026-09-13).**
  - **Bound.** Suppose a pair follows `F` acting on points, intervals, finite configurations or the Cantor set on all
    but a `δ` fraction of points. Then `d(AB,BA) ≤ 4δ + k sqrt(6δ)` (`thompson-f-spatial-permutation-models-almost-commute`).
  - **Consequence.** Truncated dyadic-tree models, reservoir or depth-shuffle repairs, and the Følner windows of
    `thompson-f-end-rigid-schreier-graphs-are-amenable` cannot witness this claim.
  - **Exact profiles** (`research/artifacts/thompson-f-spatial-permutation-models-2026-09-13.md`):
    - truncations keep `δ ≈ 1/4` and relator defect `≥ 0.53`;
    - `x_0`-rays drive defect and separation to 0 together;
    - perturbed commuting pairs pay about twice their separation in defect.
  - **Gap.** A witness with separation `ε` must be `min(ε/8, ε²/(24k²))`-far from following every such action.
