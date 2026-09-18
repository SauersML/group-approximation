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
- **Lampshuffler actors (fp version dead; FP_2 open, unpromising).** For infinite
  `Γ` of type `FP_2` containing the input (e.g. Leary's group times `Z`, which is
  one-ended), `FSym(Γ) ⋊ Γ` acts faithfully and highly transitively on `Γ` with
  finitely generated point stabilizers, so it would be a faithful `[HA_2]` actor
  if it were `FP_2`. Genevois–Tessera, arXiv:2401.13520v1, Theorem 1.5 (a halo
  product with a finite `F` and infinitely many `h` with
  `⟨F, hFh^{-1}⟩ ≠ ⟨F⟩ ∗ ⟨hFh^{-1}⟩` is not finitely presented) give: "lampshuffler
  groups over infinite groups are never finitely presented" (read through fetched
  quotations). Whether some are `FP_2` is not settled there. Their mechanism
  replaces far commutations by free products, and the resulting kernels look
  non-perfect (in `Z/2 ∗ Z/2` the kernel onto `Z/2 × Z/2` is infinite cyclic), so
  the Bieri–Strebel route to `FP_2` does not suggest itself.
- **Weaker target recorded by the 1.20 lane.** An uncountable family of faithful
  `[HA_2]` actors already gives uncountably many simple `FP_2` groups
  (`uncountably-many-fp2-groups-have-faithful-ha2-actions`). One fixed finitely
  generated actor group has only countably many `[HA_2]` actions, since point
  stabilizers are finitely generated subgroups.
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
- **2026-09-18 (swarm-0917-w10-w10-z-last1, reframing): orbit-finite affine
  actors; inner case killed by element orders.**
  - Established: an FP_2 group `S ⋊ W` with `W ≤ Aut(S)` finitely generated and
    finitely many `W`-orbits on `S` acts faithfully on `S` with type `[HA_2]`.
    The action is transitive with stabilizer `W`, and pair orbits are `W`-orbits.
    The inner case `Γ × Γ ↷ Γ` needs only `Γ` FP_2, centreless and
    conjugacy-finite (`orbit-finite-fp2-affine-actors-are-faithful-ha2-actors`).
  - New route `faithful-ha2-actor-via-orbit-finite-fp2-affine-actors`: its one
    open prerequisite is
    `every-countable-group-embeds-in-an-orbit-finite-fp2-affine-actor`.
  - Class-kill: two-sided translation actors `Γ × Γ` of conjugacy-finite groups
    have finitely many element orders, so they miss `Q/Z`, `⊕ Z/n` and `V`,
    whatever finiteness is assumed of `Γ`
    (`conjugacy-finite-actors-have-finitely-many-element-orders`).
  - In the affine case the orders must come from `W`. The first open test is
    `Q/Z`: is there an FP_2 group `W ⊇ Q/Z` with an infinite, orbit-finite,
    finitely generated module `S` such that `S ⋊ W` is FP_2?
  - Torsion-free inputs of type FP reduce to
    `torsion-free-fp-groups-embed-in-fp2-conjugacy-finite-groups`, an FP_2 form of
    Osin's theorem. That claim also feeds the first part of Problem 1.20 through
    `uncountably-many-ha2-actors-via-conjugacy-finite-fp2-groups`.
