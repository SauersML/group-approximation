---
rg: 2
id: fp-clopen-transitive-full-cantor-groups-have-type-a-actions
kind: claim
title: A finitely presented full group of Cantor homeomorphisms whose local maps join any two nonempty clopen sets has a type (A) clopen action
distinct_from:
  fp-full-binary-cantor-groups-have-type-a-actions: that assumes the group contains the standard binary V acting on binary Cantor space; this replaces that hypothesis by clopen transitivity of local maps, which is invariant under conjugation by arbitrary homeomorphisms and holds for full groups of G_V times a minimal action groupoid, where no identification with the standard binary V was checked.
  full-binary-cantor-groups-have-copy-stabilizers: that proves stabilizer factorization using prefix maps of the standard V; this proves the same factorization from fullness and clopen transitivity alone.
  twisted-btb-clopen-action-is-type-a: that is the clopen action of one specific family of groups; this is a criterion for any finitely presented full group with clopen-transitive local maps.
---

**ESTABLISHED** by `fp-clopen-transitive-full-cantor-group-type-a-proof`. Not
independently reviewed.

## Statement

Let `Y` be a Cantor space and `D <= Homeo(Y)`. A *D-local map* is a homeomorphism
`f : U -> U'` between clopen subsets of `Y` such that every point of `U` has an
open neighbourhood on which `f` agrees with some element of `D`. Assume:

1. **(full)** every homeomorphism of `Y` that is D-local belongs to `D`;
2. **(clopen transitive)** for any two nonempty clopen `U, U' ⊆ Y` there is a
   D-local map `U -> U'`;
3. `D` is finitely presented.

Let `𝒮` be the countable set of proper nonempty clopen subsets of `Y`. Then the
action of `D` on `𝒮` is of type (A) in Zaremsky's sense
(`type-a-action-gives-boone-higman-for-subgroups`):
- it is faithful;
- the stabilizer of `U ∈ 𝒮` is isomorphic to `D × D`, hence finitely generated;
- there are at most 16 orbits of ordered pairs, hence finitely many orbits of
  two-element subsets.

So every subgroup of `D` has solvable word problem, embeds in a finitely
presented simple group (Zaremsky, Corollary B), and lies in the permutational
class `B_A`.

## Relation to the standard-V version

If `V <= D` for the standard binary `V`, clopen transitivity holds (prefix
matching of cone decompositions), so this contains
`fp-full-binary-cantor-groups-have-type-a-actions`. Hypotheses 1 and 2 are
preserved by conjugation by any homeomorphism, so no binary model of `Y` is
needed.
