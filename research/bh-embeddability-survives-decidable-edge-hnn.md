---
rg: 2
id: bh-embeddability-survives-decidable-edge-hnn
kind: claim
title: HNN extensions over finitely generated edges with decidable membership preserve embeddability into finitely presented simple groups
distinct_from:
  bh-embeddability-forces-decidable-edge-membership: that proves decidable edge membership is NECESSARY and that the unrestricted closure fails; this asserts that with that hypothesis the closure holds, which is open.
  boone-higman-type-a-class-closed-under-finite-extensions: that is a permanence of the type (A) class under finite extensions; this is a permanence of embeddability into finitely presented simple groups under HNN extensions with infinite, finitely generated associated subgroups.
---

Let `A` be a finitely generated group that embeds in a finitely presented
simple group. Let `C_1, C_2 <= A` be finitely generated subgroups with decidable
membership problems in `A`, and let `phi : C_1 -> C_2` be an isomorphism given
on generators. Then the HNN extension `A*_phi` embeds in a finitely presented
simple group.

**OPEN.** By `bh-embeddability-forces-decidable-edge-membership`, the
decidability hypothesis is necessary, and without it the statement is false.
With it, `A*_phi` has solvable word problem by Britton's reduction, so no
decidability obstruction remains.

## Attempts

1. **Twisted Brin--Thompson group of the tree action.** On the Bass--Serre tree
   of `A*_phi`, distance between two vertices is an invariant of two-element
   subsets, and it takes infinitely many values. So the tree action has
   infinitely many orbits of two-element subsets, and
   `twisted-brin-thompson-finite-presentation-criterion` does not apply to it.
   *Dies* for this action. Other faithful actions of `A*_phi` are untried.
2. **Pass to the envelope first.** Embed `A <= S` with `S` finitely presented
   simple, and form `S*_phi`. It is finitely presented because `C_1, C_2` are
   finitely generated, and it contains `A*_phi`. Two gaps remain. Membership of
   `C_i` in `S` need not be decidable even when it is decidable in `A`; it is if,
   for example, `A` has decidable membership in `S`. And `S*_phi` is not simple:
   a finitely presented simple overgroup of it is Boone--Higman for HNN
   extensions of finitely presented simple groups, no easier than the claim.
   *Deferred.*
3. **Iteration cannot reach FA inputs.** By
   `fa-subgroups-of-graph-towers-lie-in-base-pieces`, iterating this permanence
   along a tower reaches an input with property FA only through the base group.
   This does not refute the claim; it limits what iterating it can prove.
