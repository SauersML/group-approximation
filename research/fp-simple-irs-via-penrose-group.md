---
rg: 2
id: fp-simple-irs-via-penrose-group
kind: route
title: A finitely presented derived Penrose tiling group has a nontrivial ergodic IRS
target: fp-infinite-simple-group-with-nontrivial-irs
requires:
  - penrose-tiling-group-is-an-amenable-orbit-full-group
  - penrose-derived-full-group-is-finitely-presented
---

Let `S = D(𝒫)`, with `Lambda = P/<w_1, w_2> ≅ Z^2 ⊕ Z/5` acting freely on the cut torus
`X` and `mu` the lifted Lebesgue measure
(`penrose-tiling-group-is-an-amenable-orbit-full-group`). `S` is infinite, simple and,
by the second prerequisite, finitely presented.

**The action.** `S ≤ [[Lambda ~ X]]` preserves `mu`. Translation by the dense subgroup
`P / <w_1, w_2>` of the torus is ergodic for Lebesgue measure: an invariant `L^2`
function has Fourier coefficients supported on characters trivial on a dense subgroup,
hence only the constant one. As in `fp-simple-irs-via-labbe-shift`, 3-cycles of small
translated clopen sets move each point to any point of its `Lambda`-orbit, so the
`S`-invariant sets are `Lambda`-invariant and `mu` is `S`-ergodic.

**Nontrivial IRS.** Let `nu = Stab_* mu`.
- `nu != delta_S`: a nontrivial element of `S` moves a nonempty open set, which has
  positive measure by full support.
- `nu != delta_{1}`: a 3-cycle on three small pairwise disjoint translates of a clopen
  set lies in `S` (Item "Infinite" of `penrose-tiling-group-amenable-orbit-citation`) and
  fixes a set of positive measure.

So `S` witnesses `fp-infinite-simple-group-with-nontrivial-irs`. ∎
