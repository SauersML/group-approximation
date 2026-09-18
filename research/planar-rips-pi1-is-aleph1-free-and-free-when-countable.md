---
rg: 2
id: planar-rips-pi1-is-aleph1-free-and-free-when-countable
kind: claim
title: "The fundamental group of a Rips complex of any planar set is aleph_1-free, and free when the set is countable"
distinct_from:
  planar-rips-complexes-have-free-first-homology: that claim is about first homology, the abelianization; freeness of an abelianization does not give freeness of the group, and this claim is the nonabelian statement
  planar-rips-projection-is-a-pi1-isomorphism: that claim is about one finite set and its shadow; this one is about arbitrary, possibly infinite, planar sets and uses the projection theorem only as input
  some-infinite-planar-set-has-a-non-wedge-rips-complex: that claim asks for a counterexample to the infinite reading of Zaremsky 4.2; this one rules out fundamental-group certificates for such a counterexample when the set is countable, and leaves the question itself open
---

Let `X ⊆ R^2` be arbitrary, `r > 0`, and let `R_r(X)` be the Vietoris–Rips
complex in either convention (`≤ r` or `< r`). Let `x_0 ∈ X`, and put
`G = π_1(R_r(X), x_0)`. Then:

1. `G` is `ℵ_1`-free: every countable subgroup of `G` is free.
2. If `G` is countable, then `G` is free. This holds in particular whenever
   `X` is countable.

Every point of `|R_r(X)|` is joined by a path to a vertex, so these statements
cover every component and every base point.

**Why it matters.**

- The artifact
  `research/artifacts/zaremsky-4-02-planar-rips-infinite-2026-09-16.md` §6
  proved only that `G` is locally free. It recorded the missing free-factor
  lemma as the place where freeness of `π_1` died, and noted that a non-free
  `π_1` would itself certify a non-wedge.
- This claim closes that gap for countable `X`. A countable planar set can
  never be a counterexample to the infinite reading of Zaremsky 4.2 by reason
  of its fundamental group.
  - By `planar-rips-complexes-have-free-first-homology`, `H_1` cannot certify
    one either.
  - So any such certificate must use `π_{≥2}`, `H_{≥2}`, the action of `π_1`
    on higher homotopy, or `k`-invariants.
- For uncountable `X` the gap narrows to a single, precisely stated point,
  recorded under Attempts.

**Proof.** In `planar-rips-pi1-is-aleph1-free-and-free-when-countable-proof`.
The proof takes the images of finite stages, which stabilise by the
Hopfian property. The planar free-factor lemma
`planar-polyhedron-inclusions-have-free-factor-pi1-images` then shows that
each stable image is a free factor of every larger one. Countable subgroups
lie in a chain union of free factors.

## Attempts

- 2026-09-18 (swarm-0917-w10-w10-z-break): proved parts 1 and 2 by the route
  above.
- 2026-09-18 (swarm-0917-w10-w10-z-break), open for uncountable `X`: is `G`
  free?
  - Here `G = ⋃_Y J_Y` over countable `Y ⊆ X`, where `J_Y` is the image of
    `π_1(R_r(Y))`. Each `J_Y` is free by part 1.
  - Take `|X| = ℵ_1` and a continuous chain `(Y_α)_{α < ω_1}` of countable
    sets exhausting `X`. If each `J_{Y_α}` were a free factor of
    `J_{Y_{α+1}}`, then a transfinite union of bases would make `G` free.
  - The route only gives this for finite `Y`. For countable `Y`, it would need
    a coherent choice of complements across the whole chain `J_{E_n}`, a
    "nonabelian Nöbeling". The abelian version is what
    `profinite-integer-function-groups-are-free` supplies for `H_1`.
  - Unions of free factors need not be free factors. In `F(x_1, x_2, …)`, the
    subgroups `⟨x_1 x_2^2, …, x_n x_{n+1}^2⟩` are free factors of
    `F(x_1, …, x_{n+1})`, but their union is not a free factor of the whole
    group.
  - So the uncountable case needs genuinely new input: either a geometric
    coherence of complements or a non-free `ℵ_1`-free example.
