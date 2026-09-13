---
rg: 2
id: coarsely-injective-groups-rips-proof
kind: route
title: Coarse ball intersections verify Zaremsky's small-ball criterion on an orbit
target: coarsely-injective-groups-have-contractible-rips-complexes
requires:
  - small-ball-criterion-gives-contractible-rips-complexes
  - group-rips-complexes-are-cayley-graph-flag-complexes
---

Notation as in the target claim.

**Step 0: an integer metric on `G`.** `Stab(x_0)` is finite by properness, hence trivial.
So `ρ(g, h) = d(g x_0, h x_0)` is a left-invariant metric on `G`. Put `ρ' = ⌈ρ⌉`; it is a
metric since `⌈a⌉ + ⌈b⌉ ≥ ⌈a + b⌉`. For integers `t`, `ρ ≤ t` iff `ρ' ≤ t`, so
`VR_t(G, ρ') = VR_t(G, ρ)`. Each `ρ'`-ball of radius `t` is `g(T_t ∪ {1})`, which is
finite by properness and of size independent of `g`; so condition (*) holds.

**Step 1: coarse midpoints.** For `x, y ∈ E` with `d(x, y) = L`, the balls `B(x, L/2)`
and `B(y, L/2)` satisfy the hypothesis, so some `p` has `d(p, x), d(p, y) ≤ L/2 + δ`.
Halving `m` times gives a chain from `x` to `y` whose steps are at most
`L/2^m + 2δ`, hence at most `2δ + 1` for large `m`.

**Step 2: `T_t` generates for `t ≥ 2D + 2δ + 1`.** Given `g`, take such a chain from `x_0`
to `g x_0` and orbit points `g_i x_0` within `D` of its points, with `g_0 = 1` and the last
one `g`. Consecutive `g_i x_0` are within `2D + 2δ + 1 ≤ t`, so
`g_i^{-1} g_{i+1} ∈ T_t ∪ {1}`. `T_t` is finite by properness and symmetric.

**Step 3: the criterion.** Let `t > t_0` be an integer, `r_t = ⌈t/2 + δ + D⌉`, and
`S ⊆ G` with `ρ'`-diameter `t`; then `ρ(s, s') ≤ t` on `S`. Since `t ≥ 2δ + 2D + 2`,
`r_t < t`. Let `Y_S = {y' ∈ G : ρ'(y', s) ≤ r_t` for all `s ∈ S}`, the centres of the
radius-`r_t` balls containing `S`. Consider the balls `B(s x_0, t/2)` for `s ∈ S` and
`B(y' x_0, r_t)` for `y' ∈ Y_S`. They satisfy the hypothesis:

- `ρ(s, s') ≤ t = t/2 + t/2`;
- `ρ(s, y') ≤ r_t ≤ t/2 + r_t`;
- `ρ(y', y'') ≤ ρ(y', s) + ρ(s, y'') ≤ 2 r_t`.

So some `p ∈ E` has `d(p, s x_0) ≤ t/2 + δ` for all `s ∈ S` and `d(p, y' x_0) ≤ r_t + δ` for
all `y' ∈ Y_S`. Choose `y ∈ G` with `d(p, y x_0) ≤ D`. Then:

- `ρ(y, s) ≤ t/2 + δ + D`, so `ρ'(y, s) ≤ r_t`: `S` lies in the `ρ'`-ball of radius
  `r_t < t` about `y`, and `y ∈ Y_S`;
- for every centre `y' ∈ Y_S`, `ρ(y, y') ≤ D + r_t + δ ≤ t/2 + 2δ + 2D + 1 ≤ t`, since
  `t ≥ 4δ + 4D + 2`; so `ρ'(y, y') ≤ t`.

These are the hypotheses of `small-ball-criterion-gives-contractible-rips-complexes` for
every `t > t_0`. Hence `VR_t(G, ρ')` is contractible for all `t > t_0`.

**Step 4: a word metric.** `ρ(g, h) ≤ t` iff `g^{-1} h ∈ T_t ∪ {1}`, so
`VR_t(G, ρ') = Flag(Cay(G, T_t))`. By `group-rips-complexes-are-cayley-graph-flag-complexes`
(item 1), this is `R_1(G, T_t)`. ∎

Model test: `Z` acting on `R` (injective, `δ = 0`) by translations, `x_0 = 0`, `D = 1/2`:
`t_0 = 4`, and for `t = 5`, `T_5 = {±1, …, ±5}`; the clique complex of `Cay(Z, T_5)` is
`VR_5(Z)`, which is contractible. ✓ The torsion-free hypothesis is used only for
injectivity of the orbit map.
