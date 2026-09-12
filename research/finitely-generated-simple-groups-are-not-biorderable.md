---
rg: 2
id: finitely-generated-simple-groups-are-not-biorderable
kind: claim
title: No nontrivial finitely generated simple group admits a bi-invariant total order
distinct_from:
  formalizable-binary-pairs-over-biorderable-groups-are-affine: that is the one-track affine rigidity theorem over bi-orderable hosts; this shows its hypothesis fails on every finitely generated simple host, so the rigidity theorem and its marker refutation never reach the hosts the Kaplansky payoff needs.
artifacts:
  - research/artifacts/stable-formalizability-on-simple-hosts-2026-09-12.md
---

A finitely generated simple group `G ≠ 1` has no total order invariant under left and right
multiplication.

**Proof sketch.**
- An abelian simple group is `Z/p`, which has torsion.
- A finitely generated bi-ordered `G ≠ 1` has a maximal proper convex subgroup `C`: the union of all
  proper convex subgroups.
- `C` is normal, because conjugation preserves the order.
- `G/C` is an Archimedean bi-ordered group, so by Hölder's theorem it embeds in `(R, +)`.
- So `G` has a nontrivial abelian quotient and is not nonabelian simple.

**Use in family F.**
- `formalizable-binary-pairs-over-biorderable-groups-are-affine` and the marker refutations over `Z`
  and `Q` (`binary-left-inverse-pairs-need-not-be-formalizable`,
  `marker-involution-over-rationals-is-not-virtually-formalizable`) do not apply to any finitely
  generated simple host, not even at one track.
- The pushforward obstruction of `formal-pairs-push-along-quotients-of-the-encoder-memory-group` is void
  once the encoder memory generates such a host.

**Trust surface.** Hölder's theorem (1901), that Archimedean ordered groups embed in `(R, +)`, is
imported at statement level.

Proof: artifact Section 2, route `fg-simple-groups-not-biorderable-proof`.
