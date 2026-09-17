---
rg: 2
id: f-free-groups-are-closed-under-recurrent-extensions
kind: claim
title: "Groups without copies of F, and groups without sections isomorphic to F, are closed under extensions, directed unions and recurrent extensions, so no such closure of an F-free base reaches Thompson's F"
distinct_from:
  thompson-f-has-no-free-subgroups: that says F avoids free subgroups; this says the operations used to build amenable groups (extensions, unions, recurrent actions with amenable stabilizers) never produce a copy of F from groups that lack one.
  every-subgroup-of-thompson-f-is-ea-or-contains-f: that is the open Brin–Sapir dichotomy inside F; this is an unconditional closure theorem for arbitrary groups.
  thompson-f-recurrent-orbits-have-stabilizers-containing-f: that is the stabilizer theorem for a single recurrent orbit; this packages it with extension and union closure into a class obstruction.
  lea-permanence-closure-fp-kazhdan-groups-are-residually-finite: that is a permanence closure for LEA/Kazhdan groups; this is a closure for F-freeness under recurrent extensions.
---

**ESTABLISHED.** **Definitions.**
- A group `G` is a *recurrent extension* of a class `𝒞` if `G` is finitely generated
  and has an action with a recurrent orbit `G·x` whose stabilizer `G_x` lies in `𝒞`.
- `𝓕` is the class of groups with no subgroup isomorphic to `F`.
- `𝓓` is the class of groups with no section, meaning a quotient of a subgroup,
  isomorphic to `F`.

**Theorem T1.** `𝓕` is closed under
1. subgroups,
2. extensions (`N ◁ G` with `N, G/N ∈ 𝓕` implies `G ∈ 𝓕`),
3. directed unions,
4. recurrent extensions.

**Theorem T2.** `𝓓` is closed under subgroups, quotients, extensions, directed unions
and recurrent extensions.

**Corollary (the class obstruction).** Let `𝓑 ⊆ 𝓕` be any class of groups. The
smallest class containing `𝓑` and closed under operations 1–4 lies in `𝓕`, so it does
not contain `F`, nor any group containing `F`. Admissible bases include:
- **residually finite groups.** `F` is not residually finite
  (`thompson-f-is-not-residually-finite`). This base contains all finitely generated
  automaton groups acting on rooted trees.
- **LEF groups.** Subgroups of LEF groups are LEF, and `F` is finitely presented
  (`thompson-f-is-of-type-f-infinity`) and not residually finite, hence not LEF
  (`finitely-presented-lef-groups-are-residually-finite`).
- **groups of locally subexponential growth.** `F` contains a copy of `Z ≀ Z`, which
  has exponential growth (proved in the route).
- any union of these bases.

If the base `𝓑 ⊆ 𝓓` is closed under sections, the closure may also use quotients. For
example, from groups of locally subexponential growth, closing under subgroups,
quotients, extensions, directed unions and recurrent extensions still misses `F`. This
closure contains every elementary amenable group.

**What is killed.** Every proof that `F` is amenable of the form "`F` is built from
known amenable groups by extensions, directed unions and the recurrence criterion
(recurrent action + amenable stabilizers)" is impossible, whatever the base of known
amenable groups, as long as the base contains no copy of `F`. Quotients may also be
used, for a section-closed base with no section `F`.
- *Invariant:* "contains a subgroup (respectively a section) isomorphic to `F`".
- *Where every member dies:* at the first step producing a group that contains `F`:
  - an extension step, where `N ∩ F_0` is trivial (so `F` lived in the quotient) or
    contains `F`;
  - a union step, where `F` is finitely generated and already lived in a member;
  - a recurrent-extension step, where the stabilizer already contained `F` (Theorem R,
    by the rank-three test plus Brin ubiquity).

In each case the offending copy of `F` was already present in an input. This also
recovers that `F` is not elementary amenable, without the Chou or Cannon–Floyd–Parry
machinery, and extends it to closures that also allow recurrence steps.

**What is not killed.** Honest scope:
- extensive amenability established by non-recurrent means, such as the rare-event
  inverted-orbit confinement of `f-dyadic-ea-iff-inverted-orbit-confinement`;
- JNdlS-type arguments whose amenability input is a groupoid of germs rather than a
  point stabilizer;
- quotients from bases that are not section-closed (every group is a quotient of a
  free, hence residually finite, group);
- analytic routes: Følner sets, Liouville measures, Ore/group-ring equations.

Proof route: `f-free-groups-closed-under-recurrent-extensions-proof`.
