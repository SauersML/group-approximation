---
rg: 2
id: robertson-steger-tile-groupoids-have-no-spatial-realization
kind: claim
title: The path groupoid of a Robertson-Steger A2 tile 2-graph has no spatial realization in any Cuntz product groupoid G_2^n
artifacts:
  - research/artifacts/nv-bernoulli-conformal-class-kill-2026-09-17.md
distinct_from:
  cmsz-pg22-rs-two-graphs-admit-no-brick-coding: that excludes edge-wise brick codings of five explicit tile 2-graphs; this excludes every continuous groupoid homomorphism that is a homeomorphism on units, for all q.
  spatial-two-graph-realizations-in-g2n-leave-the-degree-plane: that is the unconditional obstruction theorem; this is its application to Robertson-Steger tile groupoids, conditional on cocycle rigidity.
---

**OPEN.** Let `T` be a triangle presentation over `PG(2,q)` satisfying (A1)–(A3), and let
`Λ_T` be its tile 2-graph.

**Claim.** There is no continuous groupoid homomorphism `ι : G_{Λ_T} -> G_2^n` whose
restriction to the unit space is a homeomorphism onto a compact open subset of
`({0,1}^N)^n`, for any `n`.

**Consequence for the target.** In
`some-brin-thompson-group-has-an-infinite-kazhdan-subgroup`, every realization of
`[[Λ_T]] ↪ nV` obtained by conjugating through such an `ι` dies. This covers brick codings
of `Λ_T` and of all its block recodings, for every `q`.

Route: `robertson-steger-no-spatial-realization-via-rigidity`. Its only OPEN input is
`robertson-steger-two-graph-groupoids-are-cocycle-rigid`.

## Attempts

### 2026-09-19, regular rank-two isotropy, germ-rank (`swarm-0917-w14-w14-nv-break`, host-geometry) — partial, rigidity-free second route for linear `T`

**Established (new).** `regular-rank-two-isotropy-blocks-spatial-realization-in-g2n`,
with a complete proof that has `requires: []`. Suppose an ample groupoid has a unit
`x` and a subgroup `A ≅ Z² ≤ G_x^x` such that every nontrivial arrow of `A` has `x` as
an isolated fixed point. Then the groupoid has no spatial realization in any `G_2^n`,
in exactly the sense used here: injectivity off units is not assumed.

- **Named invariant.** The regular rank-two isotropy.
- **The step where every candidate dies.** A realization turns `A` into an injective
  lag map `A -> Z^n`. Any rank-two subgroup of `Z^n` contains a nonzero lag with a zero
  coordinate, and such a lag fixes a whole coordinate slice of `C^n` near `ι(x)`.
- **What it uses.** No measure, no Bernoulli pinning, no `ρ(M_1) > 1`, and no cocycle
  rigidity.
- **Proved application.** Let `Γ ≤ PGL_3(K)` contain a `Z²` in a `K`-split torus whose
  nontrivial elements have no repeated eigenvalue. Then `Γ ⋉ Ω` has no spatial
  realization, and `Γ ↷ Ω` is not conjugate to an `nV`-action on a clopen set, for
  every `n`.

**What it gives here, conditionally.** Take a linear `T` whose lattice `Γ_T` has such a
regular periodic flat, for example a division-algebra unitary lattice (item 2 of the
new claim, not established). The claim then follows for that `T` from two further
inputs, neither pinned here:

- the Robertson–Steger identification of `G_{Λ_T}` with a clopen restriction of
  `Γ_T ⋉ Ω`, up to equivalence;
- the fact that equivalence preserves "a unit with regular `Z²` isotropy". Conjugating
  by bisections does preserve isolated fixed points.

This route bypasses `robertson-steger-two-graph-groupoids-are-cocycle-rigid`.

**Where it does not reach.** The hypothesis can fail inside `G_{Λ_T}` itself. Every
rank-two isotropy group contains a lag `(a,0)`. The corresponding arrow can fix a Cantor
set. It does in `G_2^2`, and in the linear case it does when the matching lattice
element has a repeated eigenvalue (a `P^1` of fixed flags). That this is the only
mechanism is not proved. For exotic `T`, and for
characteristic-`p` `T`, regularity is not automatic.

**Next falsifiable step (finite computation).** For a doubly periodic path `x` of
`Λ_T`, the fixed set of the lag-`(ka,0)` arrow near `x` is the set of
`(ka,0)`-periodic columns through `x`. These are infinite paths in a finite graph:

- vertices are cyclic colour-1 words `w` of length `ka` (tiles `w[i] -> w[i+1 mod ka]`);
- there is an edge `w -> w'` when `w[i] -> w'[i]` is a colour-2 edge for every `i`.

`x` is regular for that arrow iff its periodic column cycle has no branching exit. The
test needs to be run for the CMSZ `q = 2` presentations, for all `k`, and likewise for
the mixed-sign lags.

- If the test passes, the claim is ESTABLISHED for that `T` with no rigidity input.
- If it fails, the germ-rank invariant cannot separate `Λ_T` from `G_2^2`, and the
  rigidity route stays necessary.

**Computation run (evidence, not proof).** Script:
`experiments/rs-germ-rank-2026-09-17/periodic_column_test.py`. It runs on the five
`q = 2` presentations of `experiments/nv-brick-coding-2026-09-17/tp_q2.json`, in the
nearest-neighbour vertex model of `rs2graph.py`. The control
`experiments/rs-germ-rank-2026-09-17/control_product.py` builds `G_2^2` in the same
model and reports every periodic point non-regular, as the Lemma predicts.

- **T#0, T#1, T#3, T#4.** Each has exactly two doubly periodic points of period
  `(3,3)`, and no other periods with `a ≤ 6`, `b = 3`. Both points are regular for
  the axis lags `(3k,0)` and `(0,3k)` for `k = 1, 2, 3`.
  - Other live 3-rows do branch: 3 of the 9 have two live successors. So the
    regularity is a property of these particular orbits, not of the whole system.
- **T#2.** Every periodic point of horizontal period `a ≤ 3` branches at some `k ≤ 3`.
  - For `a = 4`, `b = 3`, however, 12 of 22 periodic points are regular for `k = 1, 2`.
  - At `k = 1`, 40 of 42 are regular at `a = 5` and 60 of 80 at `a = 6`.
- **Not tested.** All multiples `k` (the test is a separate finite graph for each `k`),
  and the mixed-sign lags `(3k, -3l)`. The mixed-sign lags are saddles and need a
  helical transfer graph along level sets of `3l·i + 3k·j`.

So the germ-rank hypothesis survives every finite test so far on all five `q = 2`
presentations, at explicit points. What remains is a uniform-in-`k` argument, for
example a determinism property of live rows, plus the saddle lags. With both, the
target is ESTABLISHED for those `T` with no rigidity input.
