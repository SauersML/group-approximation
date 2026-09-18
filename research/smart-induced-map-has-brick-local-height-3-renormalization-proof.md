---
rg: 2
id: smart-induced-map-has-brick-local-height-3-renormalization-proof
kind: route
title: Deleting the innermost cell turns each level-(k+1) SMART move into the level-k move of the same type
target: smart-induced-map-has-brick-local-height-3-renormalization
requires:
  - smart-induced-on-genuine-moves-has-exact-tripling
  - brin-thompson-first-return-maps-lie-in-kv
artifacts:
  - research/artifacts/gq-gq-nv-obstruct-smart-renormalization.md
  - research/artifacts/gq-affq-smart-renormalization-validation.md
---

Lane gq-nv-obstruct. Reviewed PASS by gq-referee-a (12b5beb4a) and gq-referee-b (b6d33ae8e). A priority
check by gq-lit-arxiv found no prior result (e78b09c00, bounded search).

**Imported, verbatim.** Callard–Salo, arXiv:2208.00685v3, `distortion-1-smart.tex`: the 8-state table
(l. 2–35), and Proposition `prop:smart-moves` (l. 52–97) with the recursions in its proof (l. 100–212).

**Inputs from the graph.** `smart-induced-on-genuine-moves-has-exact-tripling` supplies three things:
- `Y`, the genuine level-0 moves, and its bounded return, proved directly;
- `U = F_Y` up to brick-local conjugacy into `2V`, through `brin-thompson-first-return-maps-lie-in-kv`;
- exactly `3^k` consecutive `Y`-points in each level-`k` move.

**Steps.** They are in `research/artifacts/gq-gq-nv-obstruct-smart-renormalization.md`.
- §1 is the table of first `Y`-points of level-1 moves and the four edits. `A = {i_0 = 0}` is read at
  radius 1, and `Y = A ⊔ UA ⊔ U^2A`, `U^3A = A`.
- §2 is the lemma `φ(C1_K(x,s_+,s_*,ρ)) = C0_{K-1}(x,s_+,s_*,ρ)`, by induction on `K`. The side of the
  extra cell and the junction values `β` do not depend on the level.
- §3 proves `φ U^3 = U φ` on a dense subset of `A`, the points where `y` and `U^3 y` share a finite-level
  move. It extends to all of `A` by continuity.
- §1 also shows that `φ: A -> Y` is a brick-local homeomorphism. It stays brick-local after transport
  into `2V`. ∎
