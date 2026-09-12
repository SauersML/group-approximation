---
rg: 2
id: magnus-hnn-permanence-forces-one-relator-boone-higman
kind: claim
title: If Magnus-subgroup HNN extensions preserve finitely presented simple envelopes, then every one-relator group has one
distinct_from:
  bh-embeddability-survives-magnus-subgroup-hnn: that is the open permanence premise; this is the established implication from that premise to the one-relator problem, proved by induction on relator length.
  one-relator-groups-satisfy-boone-higman: that is the open conclusion; this is only the implication and establishes nothing about the premise.
  fa-subgroups-of-graph-towers-lie-in-base-pieces: that limits tower permanence for inputs with property FA; this is a tower-permanence argument for one-relator inputs, which lack property FA once they have two generators (their abelianization is infinite), so that obstruction does not arise.
  decidable-groups-embed-in-decidable-edge-towers: that asks, openly, for every decidable input to lie in a decidable-edge HNN tower over an embeddable base; for one-relator inputs this claim builds such a tower from the Magnus--Moldavanskii hierarchy, with virtually free bases, and proves the implication along it.
artifacts:
  - research/artifacts/one-relator-boone-higman-2026-09-12.md
---

**ESTABLISHED (conditional theorem).** Assume
`bh-embeddability-survives-magnus-subgroup-hnn`. Then every one-relator group
embeds in a finitely presented simple group, that is,
`one-relator-groups-satisfy-boone-higman` holds.

The proof is `magnus-hnn-permanence-forces-one-relator-bh-proof`. It is an
induction on relator length:
- **Bottom:** virtually free groups `Z/k * F`, which are hyperbolic.
- **Step:** a letter of exponent sum zero splits the group as a Magnus-subgroup
  HNN extension of a one-relator group with a shorter relator. When no letter
  has exponent sum zero, Moldavanskii's trick embeds the group in one where some
  letter does.

## What the implication consumes

- **Two kinds of premise data.** The premise is applied to shift data only
  (index chains, top letters dropped from `Y_1`, bottom letters from `Y_2`),
  and to empty associated subgroups, which adjoin free factors. For shift data
  the HNN extension is again a one-relator group. So on the data it consumes,
  the premise is equivalent to the conclusion. The implication is an
  induction-step reformulation: while climbing, the base may be assumed to
  embed.
- **Bottom of the induction.** Only `hyperbolic-groups-satisfy-boone-higman` is
  used, and only for `Z/k * F_m`.
- **Decidability.** None is used explicitly. It enters through
  `magnus-hnn-permanence-from-decidable-edge-permanence`, Magnus's solution of
  the generalized word problem.
