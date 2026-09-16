---
rg: 2
id: planar-rips-complexes-have-free-first-homology
kind: claim
title: "The first integral homology of the Rips complex of any planar set, finite or infinite, is free abelian"
distinct_from:
  planar-rips-projection-is-a-pi1-isomorphism: that claim is about finite sets and gives pi_1 through the shadow; this one is about arbitrary, possibly uncountable, sets, where no single shadow exists, and gives freeness of H_1 only
  some-infinite-planar-set-has-a-non-wedge-rips-complex: that claim asks for an infinite counterexample; this one shows first homology cannot certify one
artifacts:
  - research/artifacts/zaremsky-4-02-planar-rips-infinite-2026-09-16.md
---

Let `X ⊆ R^2` be any subset, `r > 0`, and let `R_r(X)` be the Rips complex in
either convention (simplices of diameter `≤ r`, or `< r`). Then
`H_1(R_r(X); Z)` is a free abelian group.

More precisely, `H_1(R_r(X); Z)` is isomorphic to a subgroup of `C(Ω, Z)`, the
group of continuous integer-valued functions on a profinite space `Ω`. Here
`Ω` is the inverse limit, over finite `F ⊆ X`, of the pointed finite sets
"bounded components of the complement of the shadow of `F`, plus `∞`".

**Consequences.**

- For finite `X` this also follows from
  `planar-rips-projection-is-a-pi1-isomorphism`. The new content is for
  infinite `X`, where `H_1(R_r(X))` is a directed colimit of free groups. A
  colimit of that kind need not be free, for example `Z[1/2]`.
- Freeness of `H_1` is necessary for a wedge of spheres, so no infinite
  counterexample to Zaremsky 4.2 can be certified by `H_1`. A certificate has
  to use `π_1` beyond its abelianization, `H_q` with `q ≥ 2`, or finer
  structure.
- The artifact also proves that `π_1(R_r(X))` is locally free for every planar
  `X` (Hopfian stabilization of images). Whether it is free is not settled
  there.

## Attempts

- Proof in the companion route
  `planar-rips-complexes-have-free-first-homology-proof`, with details in
  `research/artifacts/zaremsky-4-02-planar-rips-infinite-2026-09-16.md` §2.
