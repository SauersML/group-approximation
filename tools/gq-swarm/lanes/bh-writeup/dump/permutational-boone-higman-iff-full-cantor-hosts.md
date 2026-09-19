---
rg: 2
id: permutational-boone-higman-iff-full-cantor-hosts
kind: claim
title: Permutational Boone--Higman is equivalent to embedding every decidable group in a finitely presented full group of Cantor homeomorphisms with clopen-transitive local maps
distinct_from:
  permutational-boone-higman-conjecture: that is the conjecture itself, stated for type (A) actions on abstract sets; this proves it equivalent to a statement about finitely presented full groups of Cantor homeomorphisms, with no set action and no pair-orbit condition in the hypothesis.
  permutational-boone-higman-iff-finitary-alternating-hosts: that is the finitary equivalence, with hosts containing the finitary alternating group of the set acted on; this is the Cantor equivalence, with full clopen-transitive hosts, and the two together show the three host classes coincide.
  fp-clopen-transitive-full-cantor-groups-have-type-a-actions: that is the one-group criterion, the backward direction here; this adds the converse, namely that the canonical permutational host is already full and clopen transitive, so the equivalence is exact.
  fp-cantor-groups-containing-v-type-a-iff-clopen-stabilizer-fg: that drops fullness and isolates finite generation of one clopen stabilizer as the remaining condition for hosts containing standard V; this keeps fullness, where that condition is automatic, and states the resulting equivalence with the conjecture.
  decidable-groups-embed-in-fp-locally-moving-groups: that is the open locally moving host statement, whose Cantor branch was recorded as separated from Boone--Higman by finite presentability of the full closure; this shows the canonical host needs no closure, so its Cantor branch with a full host is exactly permutational Boone--Higman.
---

**ESTABLISHED** by `pbh-full-cantor-hosts-proof` (lane proof, elementary, assembling
landed nodes; not independently reviewed). No priority claimed.

## Definitions

Let `Y` be a Cantor space and `D <= Homeo(Y)`. As in
`fp-clopen-transitive-full-cantor-groups-have-type-a-actions`, a *D-local map* is a
homeomorphism `f : U -> U'` between clopen subsets of `Y` such that every point of `U`
has an open neighbourhood on which `f` agrees with some element of `D`. Call `D` a
**full clopen-transitive Cantor host** when

1. **(full)** every D-local homeomorphism of `Y` lies in `D`;
2. **(clopen transitive)** for any two nonempty clopen `U, U' ⊆ Y` there is a D-local
   map `U -> U'`.

## Statement

For every group `H` the following are equivalent.

1. `H` embeds in a finitely presented group with an action of type (A), that is,
   `H` lies in the permutational class `B_A`.
2. `H` embeds in a finitely presented full clopen-transitive Cantor host.

Consequently `permutational-boone-higman-conjecture` is equivalent to: every finitely
generated group with solvable word problem embeds in a finitely presented full group of
Cantor homeomorphisms whose local maps are clopen transitive.

The equivalence holds per input, with no finite generation or decidability hypothesis on
`H`.

In (1 => 2) the host is the twisted Brin--Thompson group `SV_{Γ_0}` of the given actor
`Γ_0 ↷ S`, acting on the Cantor cube `C^S`: it is finitely presented
(`twisted-brin-thompson-finite-presentation-criterion`), simple, contains `Γ_0`, and the
proof shows it is full and clopen transitive. In (2 => 1) the actor is the host itself,
acting on its proper nonempty clopen subsets
(`fp-clopen-transitive-full-cantor-groups-have-type-a-actions`).

## Hosts

The proof also verifies fullness and clopen transitivity for the Brin--Thompson groups.
For every `n >= 1`, `nV` is a finitely presented full clopen-transitive Cantor host, so
it carries a type (A) action on the proper nonempty clopen subsets of `C^n`, with point
stabilizers `nV x nV`. Hence every subgroup of `nV` lies in `B_A`, has solvable word
problem and embeds in a finitely presented simple group
(`type-a-action-gives-boone-higman-for-subgroups`). New in this graph:

- **Virtually special groups.** Every group with a finite-index subgroup embedding in a
  finitely generated right-angled Artin group lies in `B_A`, by
  `virtually-special-groups-embed-in-some-brin-thompson-group`. The source's list of such
  groups includes all finitely generated Coxeter groups, all limit groups, all surface and
  graph braid groups, all one-relator groups with torsion, all compact nonpositively
  curved 3-manifold groups and all finite-volume hyperbolic 3-manifold groups.
- **Cubulated hyperbolic groups.** Every hyperbolic group acting properly and cocompactly
  on a CAT(0) cube complex lies in `B_A`, by
  `cubulated-hyperbolic-groups-embed-in-some-brin-thompson-group`.
- **The additive rationals.** `Q` lies in `B_A`, by
  `rationals-embed-in-brin-thompson-group-2v`. Note `Q` is not finitely generated, so the
  finitely generated linear results do not cover it.

**These three corollaries are not new to the literature.** Belk--Fournier-Facio--Hyde--Zaremsky
Remark 3.5, quoted in `bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh`, already lists
every finitely presented simple group of Cantor homeomorphisms containing the commutator
subgroup of a Higman--Thompson group as satisfying permutational Boone--Higman, and
`V <= nV`. What the equivalence adds is that `nV` and `SV_G` are themselves type (A)
actors, which is what transfers to subgroups directly, and the exact reformulation above.

## What the equivalence does and does not buy

- **It removes the pair-orbit condition from the hypothesis.** Fullness plus clopen
  transitivity are conjugation-invariant conditions on a group of homeomorphisms; the
  finitely many pair orbits and the finitely generated point stabilizers are then
  automatic, the latter because stabilizers are `D x D`.
- **The hard part is unchanged.** It is still finite presentability of a host that
  contains a prescribed decidable group. `complexity-bounded-host-classes-are-not-universal`
  applies verbatim: the hosts for all inputs cannot share a recursive bound on
  word-problem complexity.
- **It closes one recorded gap.** `decidable-groups-embed-in-fp-locally-moving-groups`
  records that on Cantor hosts the distance from that claim to Boone--Higman is finite
  presentability of the full closure `[[Γ]]`. For the canonical permutational host no
  closure is needed, since `SV_{Γ_0}` is already full.
