---
rg: 2
id: type-a-actors-have-no-proper-power-cyclic-edge-splittings
kind: claim
title: A group with a faithful pair-orbit-finite action with finitely generated stabilizers has no irreducible splitting over a finite group or with a cyclic piece conjugate to a proper power; so the Baumslag--Gersten group and BS(m,n) with |m| != |n| carry no type (A) action
distinct_from:
  type-a-actors-split-only-over-orbit-finite-edges: that is the general orbit-finiteness theorem for vertex and edge stabilizers; this is its consequence for finite edge groups and for cyclic pieces carrying a proper-power conjugation, through the regular-orbit count.
  type-a-actors-have-no-infinite-virtually-central-subgroup: that excludes actors with an infinite virtually central subgroup, such as BS(m,m) and unimodular splittings; this excludes the non-unimodular ones, BS(m,n) with |m| != |n| and the Baumslag--Gersten group, which have no infinite virtually central subgroup.
  baumslag-gersten-group-satisfies-boone-higman: that is the open embedding question for BG, which records that no type (A) action of BG was found; this proves that none exists, while saying nothing about type (A) overgroups of BG.
  almost-automorphism-conjugate-to-proper-power-is-equicontinuous: that uses the same proper-power relation to exclude Higman--Thompson and Rover--Nekrashevych hosts; this uses it to exclude the group as its own type (A) actor, through an orbit count rather than equicontinuity.
---

**ESTABLISHED** through `type-a-actors-have-no-proper-power-cyclic-edge-splittings-proof`.
Elementary, given `type-a-actors-split-only-over-orbit-finite-edges`.

## Statement

Let `G` be a finitely generated group acting **faithfully** on a set `X`, with
finitely generated point stabilizers and finitely many orbits of two-element
subsets. For example, `G` may carry an action of type (A). Let `G` act
irreducibly on a tree `T`: minimally, without inversions, without a fixed
vertex, and without an invariant end. Then:

- **(a) Finite edges.** No edge stabilizer of `T` is finite.
- **(b) Proper-power cyclic pieces.** No vertex or edge stabilizer contains, with
  finite index, an infinite cyclic group `<c>` such that `c^p` is conjugate in
  `G` to `c^q` for some integers with `|p| != |q|`.

**The invariant.** Suppose `<c>` has finitely many orbits on `X`. Let `r(c)` be
the number of its infinite orbits, all of which are regular. Then `r` is
conjugation invariant and satisfies `r(c^p) = |p| r(c)` for `p != 0`. A relation
`c^p ~ c^q` with `|p| != |q|` forces `r(c) = 0`, so `X` is finite, so `G` is
finite.

## Instances

By Step 8 of `type-a-actors-split-only-over-orbit-finite-edges-proof`, the
Bass--Serre trees of `A *_C B` with `C != A, B`, and of `A *_phi` with
`C_1, C_2 != A`, are irreducible. So none of the following carries an action of
type (A):

1. **Finite edge groups.** No free product `A * B` of non-trivial groups
   carries one; in particular free groups of rank at least 2 carry none. More
   generally, no amalgam over a finite `C != A, B`, and no non-ascending HNN
   extension over a finite group, carries one. By Stallings' ends theorem (cited,
   not imported here), a finitely generated group with infinitely many ends has
   such a splitting. A two-ended group is virtually `Z`, so the virtually-central
   obstruction excludes it. So a finitely generated type (A) actor is finite or
   one-ended.
2. **Non-unimodular Baumslag--Solitar groups.** `BS(m,n) = <a, t | t a^m t^-1 = a^n>`
   with `|m|, |n| >= 2` and `|m| != |n|`: the vertex group `<a>` has `a^m ~ a^n`.
   These groups satisfy Boone--Higman (`baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman`),
   so "the input is its own type (A) actor" is strictly stronger than
   membership in the Boone--Higman class, even for inputs where Boone--Higman is
   known. `BS(m, ±m)` is excluded by the virtually-central obstruction, and
   `BS(1,n)` is ascending and not covered.
3. **The Baumslag--Gersten group.** `BG = <a, t | b a b^-1 = a^2>` with
   `b = t a t^-1` is the HNN extension of `H = BS(1,2) = <a, b | b a b^-1 = a^2>`
   along `<a> -> <b>`, `a -> b`. Neither cyclic subgroup is all of the
   non-abelian group `H`, so the tree is irreducible. The edge group is `<a>`,
   and `a ~ a^2`. So **BG has no action of type (A)**.
4. **Generalized Baumslag--Solitar groups** whose Bass--Serre tree action is
   irreducible and whose modular homomorphism takes a value of absolute value
   `!= 1`, by (b) applied to an elliptic generator.

## Scope

This constrains the actor, not the input. Any engine that proves a
Boone--Higman instance by building a type (A) action **of the input group
itself** dies at these inputs. This includes Attempt 5 of
`bh-embeddability-survives-decidable-edge-hnn` on the Magnus step that produces
BG. Type (A) overgroups are untouched. `BS(2,3)` has no type (A) action, yet it
embeds in a finitely presented simple group (Bux--Llosa Isenrich--Wu) by way of
a larger type (A) actor.
