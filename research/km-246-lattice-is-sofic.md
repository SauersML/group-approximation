---
rg: 2
id: km-246-lattice-is-sofic
kind: claim
title: Some (2,4,6) Kac-Moody lattice over a finite field of order at least 4 is sofic
distinct_from:
  kac-moody-lattice-is-non-hyperlinear-or-llp-failure: that is the non-hyperlinearity or LLP-failure dichotomy for all Caprace--Remy lattices; this is the sofic existence question for one explicit type, whose positive answer lands in the LLP-failure branch.
  compact-hyperbolic-km-regular-microstates-synchronize: that is unitary regular-branch synchronization, which would make these lattices non-hyperlinear; this is the permutation question, whose negation would be weaker than that conclusion.
  titz-witzel-soficity-is-one-finite-csp: that reduces soficity of the smallest Titz Mite--Witzel kernel to a three-permutation problem; this is the Kac--Moody counterpart, where the local charts are finite groups of Lie type and invariant random subgroup rigidity makes them free.
---

**OPEN.** For some prime power `q >= 4` the group `S_q = Lambda_q/Z` of
`km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4` is sofic.

**Stakes both ways.**
- *Yes.* `S_q` answers `hyperlinear-fp-infinite-simple-kazhdan-group` in its sofic form (route
  `hyperlinear-fp-kazhdan-via-km-246-lattice`), and `C*(S_q)` fails the local lifting property.
- *No.* For a simple finitely presented group, nonsoficity is permutation stability with trivial
  corrections. So `S_q` would be a permutation-stable Kazhdan lattice with torsion, of bounded flat
  rank. Its nonsoficity could not come from a compression triple inside it
  (`compression-triples-avoid-proper-cat0-groups`, conditional on the torsion hypothesis recorded
  there).

**The finite gate (from landed nodes).** Fix a finite presentation of `S_q`.
- By `almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial`, `S_q` is sofic iff there
  are almost actions `sigma_n` on `[d_n]`, with relator defects tending to 0, whose global fixed
  sets have proportion bounded away from 1.
- Every such sequence is then already a sofic approximation after deleting the global fixed
  points, and each finite subgroup acts freely on all but `o(d_n)` points.

**Levi form (not read at source).** Caprace--Remy import finite presentation from
Abramenko--Muhlherr 1997. This graph records that presentation as the colimit of the triangle of
finite rank-`<= 2` Levi subgroups (`triangle-colimit-llp-reduces-to-relator-local-splitting`).
For type `(2,4,6)` the vertex groups are `T.(SL_2(q) x SL_2(q))`, `T.Sp_4(q)` and `T.G_2(q)`, the
edge groups are `T.SL_2(q)`, and the face group is the torus `T`. In that form the gate reads:
- exact actions of the three vertex groups on `[d_n]`, free off `o(d_n)` points;
- pairwise agreement of the edge-group actions off `o(d_n)` points;
- not all trivial.

A sufficient certificate needs only one stable letter. Over a spanning tree of the triangle the
vertex groups form a virtually free amalgam `K_0`, and adding the third edge as an HNN letter `t`
gives a virtually free group `K` with `K/<<t>> = Lambda_q`. Exact actions of `K` on `[d_n]` in which
`t` fixes all but `o(d_n)` points, and some vertex group acts nontrivially on a proportion bounded
below, are almost actions of `Lambda_q` of the required kind.

## Attempts

- **Finite quotients.** Dead: `Lambda_q` has none for `q > 3` (Caprace--Remy, Corollary 16).
- **Ball truncations.** Dead. A finite window of the development, with trivial action on partial
  cosets, disagrees on a proportion of points bounded below by the isoperimetric constant of a
  non-amenable group.
- **Random gauges.** Dead. Two independent free `T.SL_2(q)`-structures on `[d]` agree on a
  proportion of points that tends to 0.
- **Orbit full groups.** Dead for amenable and for Haagerup acting groups:
  `kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf`,
  `irs-rigid-kazhdan-groups-avoid-haagerup-orbit-full-groups`.
- **Permanence.** Dead: see `hyperlinear-fp-infinite-simple-kazhdan-group`, Attempts.
- **Kazhdan-type inputs cannot decide it.** Two calibrations.
  - The affine Levi triangles of types `(2,4,4)` and `(2,3,6)` have colimits `Sp_4(F_q[t,t^(-1)])`
    and `G_2(F_q[t,t^(-1)])` (Caprace--Remy introduction: affine Kac--Moody groups are these
    arithmetic groups). These are residually finite and Kazhdan, so finite quotients solve their
    gates.
  - The `(2,4,6)` triangle differs from each in exactly one vertex group (`G_2` for `B_2`, or
    `B_2` for `A_2`).
  - Angle bounds and link spectral gaps, the inputs of Caprace--Thom's Proposition 4.1, hold in
    the affine types too (Oppenheim).
  - Infinite sofic Kazhdan groups are not permutation stable (Becker--Lubotzky).
  - So a proof of nonsoficity must use non-affineness of `W`, as Caprace--Remy's Theorem 15 does.
- **Quantifying Caprace--Remy's Theorem 15.** Open, and not promising as stated. Their no-quotient
  argument conjugates `U_(-alpha)` by `tau^h`, where `h` is the order of a Weyl element in a finite
  quotient, onto a root group commuting with `U_alpha`. In an almost action `tau` has no bounded
  order, and word defects grow linearly in `h`. So the argument has no direct almost-action form.
- **Measure equivalence.** Open. By `paunescu-class-is-measure-equivalence-invariant`, `S_q` lies
  in Paunescu's class, and so is sofic, iff some lattice of `Aut(X_+) x Aut(X_-)` does. Such a
  lattice is Kazhdan, and no Kazhdan group in that class is recorded.
