---
rg: 2
id: fp-cantor-groups-containing-v-type-a-iff-clopen-stabilizer-fg
kind: claim
title: A finitely presented Cantor group containing standard V acts with type (A) on clopen sets exactly when one clopen stabilizer is finitely generated
distinct_from:
  fp-full-binary-cantor-groups-have-type-a-actions: that proves type (A) for FULL finitely presented groups containing V, where stabilizers are D x D; this drops fullness and isolates the single remaining condition, finite generation of one clopen stabilizer.
  fp-groups-with-a-locally-moving-simple-subgroup-are-isolated: that shows such a group is isolated; this shows it is additionally a type (A) actor iff one stabilizer is finitely generated, so an isolated V-host outside PBH must have a non-finitely-generated clopen stabilizer.
  permutational-boone-higman-iff-finitary-alternating-hosts: that settles the finitary branch of locally moving hosts; this reduces the Cantor branch with T = V to one finiteness question.
---

**ESTABLISHED** by `fp-cantor-v-host-clopen-stabilizer-proof` (elementary, assembling
landed nodes; not independently reviewed).

## Statement

Let `Γ ≤ Homeo(C)` be finitely presented and contain Thompson's group `V` in its standard
action on `C = {0,1}^N`. Let `Ω` be the set of proper nonempty clopen subsets of `C`.
1. The action of `Γ` on `Ω` is faithful, transitive, and has at most five orbits on
   two-element subsets.
2. The following are equivalent:
   - the action of `Γ` on `Ω` is of type (A);
   - `Γ_U` is finitely generated for some `U ∈ Ω`;
   - `Γ_U` is finitely generated for every `U ∈ Ω`.
3. If these hold, every subgroup of `Γ` embeds in a finitely presented simple group
   (Zaremsky Corollary B).

## Reading for Question 4

By `fp-groups-with-a-locally-moving-simple-subgroup-are-isolated`, every such `Γ` is
isolated. So a proof of `every-decidable-group-embeds-in-an-isolated-group` through
V-hosts that does not also prove `permutational-boone-higman-conjecture` for its inputs
needs finitely presented `Γ ≥ V` in `Homeo(C)` whose clopen stabilizer is not finitely
generated. No such `Γ` is known here. In every full example the stabilizer is `D × D`.

DERIVATION
fp-cantor-v-host-clopen-stabilizer-proof
