---
rg: 2
id: type-a-actors-have-no-proper-power-cyclic-edge-splittings
kind: claim
title: A group with a faithful pair-orbit-finite action with finitely generated stabilizers has no irreducible splitting over a finite group or with a cyclic piece conjugate to a proper power; so the Baumslag--Gersten group and BS(m,n) with |m| != |n| carry no type (A) action
distinct_from:
  type-a-actors-split-only-over-orbit-finite-edges: that is the general orbit-finiteness theorem for vertex and edge stabilizers; this is its consequence for finite edge groups and for cyclic pieces carrying a proper-power conjugation, through the regular-orbit count.
  type-a-actors-have-no-infinite-virtually-central-subgroup: that excludes actors with an infinite virtually central subgroup, such as BS(m,m) and unimodular splittings; this excludes non-unimodular ones with an irreducible splitting, BS(m,n) with |m|, |n| >= 2 and |m| != |n| and the Baumslag--Gersten group, which have no infinite virtually central subgroup. The ascending case BS(1,n) is covered by neither and is the open hole ascending-baumslag-solitar-groups-have-no-type-a-action.
  baumslag-gersten-group-satisfies-boone-higman: that is the open embedding question for BG, which records that no type (A) action of BG was found; this proves that none exists, while saying nothing about type (A) overgroups of BG.
  almost-automorphism-conjugate-to-proper-power-is-equicontinuous: that uses the same proper-power relation to exclude Higman--Thompson and Rover--Nekrashevych hosts; this uses it to exclude the group as its own type (A) actor, through an orbit count rather than equicontinuity.
---

**OPEN** as stated. The route
`type-a-actors-have-no-proper-power-cyclic-edge-splittings-proof` proves parts (a) and (b)
below and the `BG`, `BS(|m|,|n| >= 2)`, finite-edge and GBS instances, from
`type-a-actors-split-only-over-orbit-finite-edges`. What is not proved is the headline in the
title: `BS(1,n)` with `n >= 2` has `|m| != |n|` but is ascending, and the route says nothing
about it. That case is now the separate hole
`ascending-baumslag-solitar-groups-have-no-type-a-action`, which the route requires. See the
2026-09-18 entry under Attempts.

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

## Attempts

- 2026-09-18 (adversarial referee pass, outcome refuted as stated): **the headline asserts a
  case the route excludes at its own calibration boundary.** Referee's reason, verbatim:
  - "The core theorem verifies: I checked every step of the route proof (regular-orbit
    invariant r, r(c^p)=|p|r(c), conjugation invariance, p,q != 0, X finite contradiction) and
    all of Steps 0-8 of the prerequisite
    type-a-actors-split-only-over-orbit-finite-edges-proof (ESTABLISHED), plus the Zaremsky
    type (A) citation, which matches the hypotheses verbatim. Parts (a) and (b) as written in
    the Statement section are correct, as are the BG, BS(|m|,|n|>=2), finite-edge and GBS
    instances. What fails is the claim's advertised statement: the title (line 5) and the
    distinct_from entry for type-a-actors-have-no-infinite-virtually-central-subgroup (line 8)
    both assert 'BS(m,n) with |m| != |n| carry no type (A) action', while the instance actually
    proved (line 51) requires |m|, |n| >= 2 and the body explicitly disclaims the rest
    ('BS(1,n) is ascending and not covered'). BS(1,n), n >= 2, has |m| != |n|, is
    non-unimodular, and has no infinite virtually central subgroup, so no other obstruction in
    the graph covers it either. That omitted case is exactly the end-fixing one: an ascending
    HNN has a G-invariant end, so Step 3 of the prerequisite proof (the unbounded case,
    discharged only by uniqueness of the end with property (P)) has nothing to say, and the
    route uses no other property separating ascending from non-ascending splittings. An
    ESTABLISHED headline that asserts a case its route explicitly excludes at its own
    calibration boundary is not established as advertised."
  - **The exact step that fails.** No step of the route proof is wrong. The gap is between the
    route's Instances section, item `BS(m,n)` ("the associated subgroups `<a^m>` and `<a^n>`
    are proper because `|m|, |n| >= 2`"), and the claim's title, which quantifies over all
    `|m| != |n|`.
  - **Demotion.** The missing statement is now
    `ascending-baumslag-solitar-groups-have-no-type-a-action` (OPEN), added to the route's
    `requires:`. The proof file is kept: everything in it stands.
