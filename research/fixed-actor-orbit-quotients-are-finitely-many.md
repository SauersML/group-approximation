---
rg: 2
id: fixed-actor-orbit-quotients-are-finitely-many
kind: claim
title: An actor with m orbits on pairs has at most 2^m orbit-quotient actors, so almost every member of an uncountable family of faithful [HA_2] actors has infinitely generated stabilizers in every finitely presented cover
distinct_from:
  perfect-orbit-quotients-of-fp2-actors-are-ha2-actors: that builds one faithful [HA_2] actor from an FP_2 actor and a perfect normal subgroup with faithful orbit partition; this counts those subgroups for a fixed actor, at most 2^(m-k), and shows the construction never multiplies cardinality.
  finite-similarity-types-bound-minimal-invariant-sets: that bounds minimal invariant sets of an ample groupoid by its similarity types, killing restriction routes over a Stein--Farley ambient; this bounds invariant equivalence relations of a permutation action by its pair orbits, killing quotient routes over a fixed [HA_2] or [A_2] actor.
  fg-groups-with-re-or-co-re-word-problem-are-countable: that confines uncountable families by word-problem complexity; this confines uncountable families of faithful [HA_2] actors by finite generation of stabilizers in finitely presented covers, which says nothing about computability.
  uncountably-many-fp2-groups-have-faithful-ha2-actions: that is the open existence claim; this is a necessary condition on any witnessing family.
---

**ESTABLISHED** by `fixed-actor-orbit-quotients-are-finitely-many-proof`
(elementary counting).

**Setting.** A group `P` acts on a set `X` with `m` orbits on `X × X`, and `k` of
them are orbits on `X`. A `P`-invariant equivalence relation `E` on `X` gives
the *orbit-quotient actor* `(P/K_E, X/E)`, where `K_E` is the kernel of
`P ↷ X/E`. A normal `N ⊴ P` has *faithful orbit partition* when the elements of
`P` that preserve every `N`-orbit are exactly the elements of `N`.

1. **Invariant relations.** `P ↷ X` has at most `2^(m-k)` invariant equivalence
   relations.
2. **Perfect orbit quotients.** At most `2^(m-k)` normal subgroups `N ⊴ P` have
   faithful orbit partition. For each, `N = K_{E_N}`, with `E_N` the
   `N`-orbit relation, and `(P/N, X/N)` is an orbit-quotient actor.
3. **Iteration.** An orbit-quotient actor of an orbit-quotient actor of
   `(P, X)` is isomorphic to an orbit-quotient actor of `(P, X)`. So all finite
   iterations of item 2
   (`perfect-orbit-quotients-of-fp2-actors-are-ha2-actors`) starting from
   `(P, X)` give at most `2^(m-k)` actors, and at most `2^(m-k)` groups
   `SV_{P/N}`.
4. **Countable class.** Let `𝒞` be the class of orbit-quotient actors of type
   [A_2] actions: `P` finitely presented, point stabilizers finitely generated,
   finitely many orbits on pairs. Then `𝒞` has only countably many members up to
   isomorphism of actions.
5. **Stabilizer obstruction.** Let `𝒜` be a set of pairwise non-isomorphic
   faithful actions `G ↷ S` of type [HA_2]. All but countably many members of
   `𝒜` have the following property. For every finitely presented group `H` and
   every surjection `π: H → G`, some point stabilizer of `H ↷ S` (acting through
   `π`) is not finitely generated.

**Consequence (class kill).** Take a route to uncountably many simple groups of
type `FP_2` through FFWZ Corollary 4.14
(`ha2-actions-give-fp2-twisted-brin-thompson-groups`). If its uncountable
parameter is any of the following, it produces only countably many groups
`SV_G`, and so only countably many isomorphism types of finitely generated
subgroups of them:
- a perfect normal subgroup of one actor;
- an invariant quotient of one actor;
- the kernel of a type [A_2] action, over countably many actors.

In every such route the parameter lands in the lattice of unions of the `m`
pair orbits, and item 1 counts that lattice. A witnessing family must vary the
actor group itself. For almost all of its members, the fp cover must act with
infinitely generated point stabilizers. Equivalently, the action is not an
orbit quotient of any type [A_2] action.
