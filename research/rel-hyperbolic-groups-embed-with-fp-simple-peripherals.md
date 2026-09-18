---
rg: 2
id: rel-hyperbolic-groups-embed-with-fp-simple-peripherals
kind: claim
title: A relatively hyperbolic group embeds in a relatively hyperbolic group whose peripheral subgroups are any chosen finitely generated overgroups, for example finitely presented simple hosts
distinct_from:
  hyperbolic-groups-satisfy-boone-higman: that is the Belk--Bleak--Matucci--Zaremsky theorem for hyperbolic inputs; this is a reduction lemma for relatively hyperbolic inputs that swaps the peripheral subgroups and proves no embedding into a simple group.
  bh-class-decidable-amalgams-from-free-products-and-hnn: that derives amalgam permanence of the Boone--Higman class from two open premises; this is an unconditional amalgam construction that preserves relative hyperbolicity, with no claim that the amalgam lies in the class.
  relatively-hyperbolic-dehn-filling: that passes to quotients which stay relatively hyperbolic; this passes to an overgroup which stays relatively hyperbolic.
artifacts:
  - research/artifacts/gq-bh-bh-relhyp-attack.md
---

**ESTABLISHED** by `rel-hyperbolic-fp-simple-peripherals-proof`. Lane proof, not
reviewed. The one deep input, Dahmani's combination theorem, was read at source.
No priority is claimed: this is a direct consequence of that theorem.

## Statement

Let `G` be a finitely generated group, hyperbolic relative to finitely generated
subgroups `P_1, ..., P_m` (representatives of the conjugacy classes of maximal
parabolic subgroups, Bowditch's definition). For each `i` let `S_i` be a finitely
generated group with an injection `P_i -> S_i`. Let `Ĝ` be the iterated amalgam

    Ĝ = S_m *_{P_m} ( ... ( S_1 *_{P_1} G ) ... ),

that is, the fundamental group of the star graph of groups with centre `G`, leaves
`S_i` and edge groups `P_i`.

1. `G` embeds in `Ĝ`, and `Ĝ` is hyperbolic relative to `{S_1, ..., S_m}`.
2. If `G` is finitely presented relative to `{P_i}` (Osin's definition) and every
   `S_i` is finitely presented, then `Ĝ` is finitely presented.
3. If every `S_i` has solvable word problem, so does `Ĝ` (trust note in the route).

## Corollary

If every `P_i` embeds in a finitely presented simple group `S_i`, then `G` embeds in
a group hyperbolic relative to the finitely presented simple groups `S_i`. That
group is finitely presented whenever `G` is finitely presented relative to `{P_i}`.
So `rel-hyperbolic-groups-with-bh-peripherals-satisfy-bh` needs to be proved only
for inputs whose peripheral subgroups are finitely presented simple groups.

## Why the reduction is useful

`bhm-singfix-condition-forces-fp-germ-groups` shows that the Belk--Hyde--Matucci
finiteness theorem forces every singular germ group of a finite germ extension of
`V` to be finitely presented. The peripheral subgroups `P_i` need not be finitely
presented, but after the reduction they are replaced by finitely presented `S_i`.
So a germ-extension construction with germ groups built from the peripherals is not
ruled out at the outset. See the Attempts of the OPEN claim for that route.
