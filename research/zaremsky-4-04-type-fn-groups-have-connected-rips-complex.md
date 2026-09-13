---
rg: 2
id: zaremsky-4-04-type-fn-groups-have-connected-rips-complex
kind: claim
title: "Zaremsky Problem 4.4 resolved: does every group of type F_n admit an (n-1)-connected Rips complex?"
root: true
distinct_from:
  zaremsky-4-03-rips-complex-of-zn-contractible: that is the question whether Z^n with its standard word metric has contractible Rips complexes at large scale; this asks, for every n, whether type F_n can always be witnessed by an (n-1)-connected Rips complex of the group for some generating set and scale
  hyperbolic-rips-complex-models-proper-actions: that is the classical theorem that large-scale Rips complexes of hyperbolic groups are finite models for proper actions; this is the question for arbitrary groups of type F_n and only (n-1)-connectivity
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 4, Problem 4,
verbatim: "If a group is of type F_n does it admit an (n − 1)-connected Rips
complex? For n = 2 the answer is yes, but for n > 2 we don't know."

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-4-04-by-yes` requires
  `type-fn-groups-have-n-minus-1-connected-rips-complexes`.
- **No**: `zaremsky-4-04-by-no` requires
  `some-type-fn-group-has-no-n-minus-1-connected-rips-complex`.

Never write a `requires: []` route into this claim.

## Reading

- A *Rips complex* of a finitely generated group `G` is `R_t(G,S)` for a
  finite generating set `S` and a scale `t >= 0`: vertex set `G`, simplices
  the finite nonempty subsets of `d_S`-diameter at most `t`. `G` acts
  simplicially, freely on vertices, cocompactly, with finite simplex
  stabilizers.
- "Admit" is existential: some `S` and some `t`. A stronger variant (every
  finite generating set, every large enough scale) is not what is asked; for
  `n = 2` both hold.
- Converse direction, standard: an (n−1)-connected Rips complex forces type
  `F_n` (Brown's criterion for proper cocompact actions with finite
  stabilizers). So the question is whether type `F_n` is always witnessed by a
  Rips complex.
- Reformulation, established in `group-rips-complexes-are-cayley-graph-flag-complexes`:
  for a given `n` the question asks whether every group of type `F_n` has a
  finite generating set whose Cayley graph has an (n−1)-connected clique
  complex, i.e. acts freely, vertex-transitively and cocompactly on an
  (n−1)-connected flag simplicial complex.
- `n = 1` is trivial. `n = 2`, every finite generating set and every
  `t >= max(1, L/2)` with `L` the longest relator: established in
  `fp-groups-have-simply-connected-rips-complexes`.

## What is known

- Essential connectivity: for `G` of type `F_n` and any `S`, every `t` has
  `t' >= t` with `π_k(R_t) → π_k(R_{t'})` zero for `k <= n−1` (Brown's criterion
  for filtrations; Alonso). The open gap is actual versus essential
  connectivity.
- Contractible at large scale, all `n`: hyperbolic groups
  (`hyperbolic-rips-complex-models-proper-actions`) and `Z^n` (Virk,
  arXiv:2405.09134; root 4.3).
- Per the open-status table `research/artifacts/zp-open-status-sections-2-4-2026-09-13-part2.md`
  (not yet read in the source by this lane): 2-dimensional RAAGs with standard
  generators (Li–Sánchez Saldaña, arXiv:2608.24279), scale 2 for triangle-free
  RAAGs (Hulbert–Zaremsky, arXiv:2608.25614), tools in Zaremsky,
  arXiv:1812.10976. Open for general `n > 2` as of 2026-09-13.

## Attempts

- 2026-09-13 (lane z4-04-fn-rips): reformulation and the `n = 2` case landed.
  In progress: level sets of CAT(0) cube complexes. When a group acts freely
  and transitively on the vertices of a level set, the Helly property of cubes
  makes the clique complex of "lie in a common cube" equal to the complex of
  cube vertex sets, which the nerve theorem identifies with the level set.
  This would cover Bestvina–Brady kernels, i.e. groups of type `F_n` not of
  type `F_{n+1}`.
