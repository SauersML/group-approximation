---
rg: 2
id: permutational-boone-higman-iff-finitary-alternating-hosts
kind: claim
title: Permutational Boone--Higman is equivalent to embedding every decidable group in a finitely presented permutation group containing the finitary alternating group
distinct_from:
  permutational-boone-higman-conjecture: that is the conjecture itself, about type (A) actors; this proves it equivalent to the finitary host statement, so the two are one problem.
  decidable-groups-embed-in-fp-locally-moving-groups: that is the open locally moving host statement with branches (top) and (fin); this shows its (fin) branch, taken for all inputs, is exactly permutational Boone--Higman, so that branch cannot separate Question 4 from Boone--Higman.
  every-decidable-group-embeds-in-an-isolated-group: that is CGP Question 4; this rules out finitary hosts as a way to answer it without proving permutational Boone--Higman.
  fp-finitary-alternating-overgroups-have-type-a-actions: that is the one-group lemma behind the backward direction; this is the equivalence over all inputs.
---

**ESTABLISHED** by `pbh-finitary-alternating-hosts-proof` (hand proof assembling landed
nodes, not independently reviewed).

## Statement

For a finitely generated group `H` the following are equivalent.
1. `H` embeds in a finitely presented group with a type (A) action.
2. `H` embeds in a finitely presented group `Γ` acting faithfully on an infinite set `X`
   with `Alt_fin(X) ≤ Γ`.

So `permutational-boone-higman-conjecture` is equivalent to: every finitely generated
group with solvable word problem embeds in a finitely presented `Γ ≤ Sym(X)` containing
`Alt_fin(X)`.

In (1 ⇒ 2) one can take `Γ = FSym(Ω) ⋊ SV_{Γ_0}`, where `Γ_0 ↷ S` is the given type (A)
actor and `Ω` is the set of proper nonempty clopen subsets of `C^S`.

## Consequences

- **Class kill for Question 4.** A construction answering
  `every-decidable-group-embeds-in-an-isolated-group` through branch (fin) of
  `fp-groups-with-a-locally-moving-simple-subgroup-are-isolated` proves permutational
  Boone--Higman for the same inputs, hence Boone--Higman for them
  (`type-a-action-gives-boone-higman-for-subgroups`). So finitary hosts carry no content
  beyond PBH, and any route to Question 4 that is weaker than Boone--Higman must use
  non-finitary hosts.
- **Isolated finitary hosts exist beyond Houghton.** `FSym(Ω) ⋊ SV_G` is finitely
  presented and isolated for each type (A) action of `G`; for `G = 1` on one point this is
  `FSym(Ω) ⋊ V` over the clopens of the Cantor set. This contrasts with free
  lampshufflers (`lampshuffler-groups-are-not-fp2-over-q`, Genevois--Tessera).
- **Same statement, same hard part.** The equivalence also holds per input, so a
  decidable `H` defeats PBH iff it has no finitely presented finitary overgroup.

DERIVATION
pbh-finitary-alternating-hosts-proof
