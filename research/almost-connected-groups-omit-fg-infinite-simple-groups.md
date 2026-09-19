---
rg: 2
id: almost-connected-groups-omit-fg-infinite-simple-groups
kind: claim
title: A locally compact group whose identity component is cocompact contains no finitely generated infinite simple subgroup, not even as an abstract subgroup
distinct_from:
  fg-infinite-simple-groups-are-minimally-almost-periodic: that excludes compact targets; this extends the exclusion to every almost connected locally compact target, through Gleason-Yamabe and the adjoint representation, with that theorem as the compact case.
  finitely-generated-linear-groups-are-residually-finite: that is Malcev's theorem for groups that are already linear; this shows that a finitely generated simple subgroup of an almost connected group is automatically linear, so Malcev applies.
  one-haagerup-factor-kills-bader-shalom-universality: that excludes Haagerup targets for Kazhdan probes only; this excludes almost connected targets for every finitely generated infinite simple probe, with no property (T) used.
---

**ESTABLISHED** through `almost-connected-groups-omit-fg-infinite-simple-groups-proof`.

Let `G` be a locally compact group whose identity component `G^0` has compact
quotient `G/G^0`. Let `S` be a finitely generated infinite simple group. Then:

1. every homomorphism `S → G` has image in `G^0`;
2. every homomorphism `S → G` is trivial. In particular `S` is not isomorphic to
   any subgroup of `G`, closed or not.

The hypothesis covers every compact group, every connected locally compact group
and every Lie group with finitely many components.

**Where this is used.** The probe for `decidable-simple-groups-embed-in-bader-shalom-lattices`
is `bader-shalom-hosting-factors-are-totally-disconnected`. There, a
just-non-compact factor with nontrivial identity component is almost connected.
So by item 2 it cannot receive the injective projection of an infinite simple
subgroup of the lattice.
