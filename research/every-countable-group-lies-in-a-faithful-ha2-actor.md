---
rg: 2
id: every-countable-group-lies-in-a-faithful-ha2-actor
kind: claim
title: Every countable group lies in an FP_2 group with a faithful action of type [HA_2]
distinct_from:
  permutational-boone-higman-conjecture: that asks for finitely presented actors of type (A) containing each finitely generated group with solvable word problem; this asks for FP_2 actors of type [HA_2] containing every countable group, with no word problem restriction.
  every-countable-group-embeds-in-a-simple-fp2-group: that is the envelope statement (Zaremsky Problem 1.25); this asks for an FP_2 overgroup with a faithful [HA_2] action, which gives that envelope through the twisted Brin–Thompson group.
  every-countable-group-embeds-in-an-fp2-group: that is Leary's theorem, which supplies FP_2 overgroups with no control of their actions; this asks the overgroup to act faithfully with finitely many orbits of pairs and finitely generated point stabilizers.
---

For every countable group `H` there is a group `G ≥ H` of type `FP_2` and a
faithful action `G ↷ S` with finitely many orbits on `S × S` and finitely
generated point stabilizers.

By `ha2-actions-give-fp2-twisted-brin-thompson-groups` this gives a simple
`FP_2` group `SV_G ≥ H`, so it answers Zaremsky Problem 1.25 positively
(route `every-countable-group-embeds-in-simple-fp2-via-ha2-actors`). It is the
`FP_2` analogue of the permutational Boone–Higman property, without the word
problem restriction.

## Attempts

- **Regular and imprimitive actions (dead).** The regular action of an infinite
  group has infinitely many pair orbits (the invariant `g^{-1}h`). An imprimitive
  wreath action of `W ≀_Y A` on `W × Y` over the regular action of `W` keeps that
  invariant on pairs inside a block, so it has infinitely many pair orbits
  whatever `A` is.
- **Finite orbits (dead).** A faithful action with all orbits finite embeds the
  group in a product of finite groups, so the group is residually finite. Inputs
  that are not residually finite need infinite orbits.
- **Highly transitive overgroups (open, hard).** Groups containing `FSym(S)` have
  one orbit of pairs. Their finiteness is the difficulty: `FSym(Z) ⋊ Z` is
  Houghton's `H_2`, which is not `FP_2`, and twisting Houghton groups by an
  infinite fibre group forces zero translation, since a permutation that agrees
  with a translation of infinite fibres outside finitely many points must
  translate by zero.
- **Perfect orbit quotients (live tool).** By
  `perfect-orbit-quotients-of-fp2-actors-are-ha2-actors`, an `FP_2` group with
  finitely many pair orbits and finitely generated stabilizers, divided by a
  perfect normal subgroup whose orbit partition is faithful, is a faithful
  `[HA_2]` actor. This moves non-recursive content into the perfect normal
  subgroup. It needs an imprimitive actor: a nontrivial normal subgroup of a
  primitive group containing `Alt_fin(S)` contains `Alt_fin(S)`, so its orbit
  partition is trivial. Leary's perfect kernels (`G_L({0}) → G_L(S)`) are
  normal in Leary's groups, not in any known type (A) actor; that is where this
  attempt stands.
