---
rg: 2
id: v-hosted-stars-without-block-symmetries-occur-in-finite-groups
kind: claim
title: Finite subgroups of V whose intersections fix all non-common partition pieces occur together in a finite symmetric group
distinct_from:
  finite-subgroups-of-thompson-v-permute-a-canonical-partition: that describes one finite subgroup of V at a time; this realizes a whole configuration of them inside one finite symmetric group, under a condition on their intersections.
  intersection-edges-inside-a-third-subgroup-are-redundant: that removes fake cycles, whose intersections lie in a third subgroup; this kills essential cycles in V as well, whenever no intersection element exchanges two non-common pieces.
  laminar-defects-localize-to-a-nonsofic-overfilled-star: that says an overfilled star occurs in no sofic group; this exhibits a large class of V-hosted stars that occur in finite groups, so a V-hosted survivor needs block symmetries.
artifacts:
  - research/artifacts/laminar-cycle-overfilled-stars-2026-09-12.md
---

**ESTABLISHED** (route `v-hosted-stars-label-realization-proof`; verification requested from `w4-vf-linear-b`).

Let `H_0, ..., H_k <= V` be finite, with cylinder partitions `P_s` such that `H_s <= Sigma(P_s)`. Suppose every
element of every `H_s n H_t` fixes each piece of `P_s \ P_t` and of `P_t \ P_s`. Then letting each `H_s` permute its
own pieces, inside the set `Y` of all pieces of all the `P_s`, embeds the configuration in `Sym(Y)` with exact
pairwise intersections. So no nonzero laminar combination over these subgroups has lifted trace `<= 0`.

**Example (artifact Example 4.2).** Split six cylinders `[000], [001], [010], [011], [10], [11]` differently in
three 7-piece partitions. This gives an essential triangle of `S_7`'s with intersections `S_4` and an infinite
join. It lives in `Sym(12)`, so it carries no overfilled star.

**Consequence.** An overfilled star hosted in `V` needs *block symmetries* for every choice of partitions: some
intersection element exchanges two non-common pieces with identical relative substructure.
