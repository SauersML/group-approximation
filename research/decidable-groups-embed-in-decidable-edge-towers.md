---
rg: 2
id: decidable-groups-embed-in-decidable-edge-towers
kind: claim
title: Every decidable finitely generated group embeds in an iterated HNN extension, over decidable edges, of a group with a finitely presented simple envelope
distinct_from:
  boone-hnn-tower-embeds-base-group: that is the embedding of the base group into Boone's specific HNN tower; this asks for a tower over a base with a finitely presented simple envelope, with decidable edge membership at every step, containing an arbitrary decidable input.
  decidable-fp-groups-embed-in-perfect-decidable-fp-groups: that embeds a decidable finitely presented group in a perfect one by HNN and amalgam steps starting FROM the input; this asks for towers whose base need not contain the input, so that permanence along the tower produces the envelope.
---

For every finitely generated group `G` with solvable word problem there are:
- a finitely generated group `B` that embeds in a finitely presented simple
  group;
- a sequence `B = K_0 <= K_1 <= ... <= K_n` in which each `K_{j+1}` is an HNN
  extension of `K_j` along finitely generated associated subgroups with
  decidable membership in `K_j`, with an edge isomorphism computable on
  generators;

such that `G <= K_n`.

**OPEN.**

## Attempts

1. **Higman and Clapham towers.** Their steps start from `G * F_k` or from `G`
   itself, so they certify the claim only when `G` already lies in a base with a
   finitely presented simple envelope. *Circular.*
2. **Machine towers from free groups.** Boone-type towers start from free groups
   with finitely generated free associated subgroups. By
   `fa-subgroups-of-graph-towers-lie-in-base-pieces`, every subgroup with
   property FA of such a tower is conjugate into the free base, hence is a free
   group with property FA, hence trivial. So a free base never reaches an
   infinite decidable FA input, such as an infinite Kazhdan group with solvable
   word problem. *Dies* for free bases.
3. **What any base must already do.** For an input with property FA the same
   claim forces `G` into a conjugate of `B`. So this claim contains
   Boone--Higman for all decidable FA inputs, and a proof must supply bases
   covering those inputs by some other mechanism. *Deferred.*
4. **Every decidable input has a decidable FA envelope, so this claim is
   Boone--Higman.** Every decidable `G` lies in `W_G = S wr C_2`, where `S` is
   an infinite decidable simple envelope. `W_G` is decidable and has property FA
   (`decidable-groups-have-decidable-fa-envelopes`,
   `fg-perfect-wreath-c2-has-property-fa`). Applying Attempt 3 to `W_G` puts `G`
   inside `B`. By `decidable-edge-tower-premise-is-equivalent-to-boone-higman`,
   this claim is equivalent to `boone-higman-conjecture`, with the converse
   given by `B = G` and `n = 0`. No tower of positive length helps any input.
   *Dies* as a reduction, pending referee (2026-09-17): the envelope and FA
   inputs are drafted but not yet fully refereed, since one of three votes was
   lost. If they survive, it upgrades Attempt 3 from "contains Boone--Higman for
   FA inputs" to full equivalence, and the claim stays OPEN exactly as long as
   the conjecture does.
