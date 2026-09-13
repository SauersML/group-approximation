---
rg: 2
id: perfect-orbit-quotients-of-fp2-actors-are-ha2-actors
kind: claim
title: Dividing an FP_2 actor by a perfect normal subgroup with faithful orbit partition gives a faithful [HA_2] actor
distinct_from:
  ha2-actions-give-fp2-twisted-brin-thompson-groups: that imports the finiteness and simplicity of SV_G for [HA_2] actions; this builds new faithful [HA_2] actions from old ones by passing to perfect quotients.
  stable-permutation-hnn-of-type-a-actor-is-type-a: that builds type (A) actors from HNN extensions realized on the same set; this builds [HA_2] actors from quotients by perfect normal subgroups acting on orbit sets, which can destroy recursive presentability.
---

**ESTABLISHED** by `perfect-orbit-quotients-of-fp2-actors-are-ha2-actors-proof`.

Let `P` be a group of type `FP_2` (over `Z`) acting on a set `X` with finitely
many orbits on `X × X` and finitely generated point stabilizers. Let `N ⊴ P` be
perfect, and suppose the only elements of `P` that preserve every `N`-orbit are
the elements of `N`. Then:

1. `P/N` acts faithfully on the set `X/N` of `N`-orbits;
2. this action has finitely many orbits on `X/N × X/N`, and its point stabilizers
   are finitely generated;
3. `P/N` is of type `FP_2`.

So `P/N ↷ X/N` is a faithful action of type `[HA_2]`, and every subgroup of `P/N`
embeds in the simple `FP_2` group `SV_{P/N}`
(`ha2-actions-give-fp2-twisted-brin-thompson-groups`).

Two facts used, both proved in the proof route:
- (L1) a finitely generated group is of type `FP_2` iff it is a finitely
  presented group divided by a perfect normal subgroup (the Bieri–Strebel
  characterization);
- (L2) a quotient of an `FP_2` group by a perfect normal subgroup is `FP_2`.

**Where it stops.** The hypothesis on `N` forces an imprimitive action: in a
primitive group containing `Alt_fin(X)` every nontrivial normal subgroup contains
`Alt_fin(X)`, which is transitive. Its use for Problem 1.25 is to place
non-recursive content in `N` while `P` stays decidable; no suitable pair
`(P, N)` is known yet (`every-countable-group-lies-in-a-faithful-ha2-actor`).
