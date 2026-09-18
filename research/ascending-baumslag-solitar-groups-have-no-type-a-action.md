---
rg: 2
id: ascending-baumslag-solitar-groups-have-no-type-a-action
kind: claim
title: The ascending Baumslag-Solitar groups BS(1,n) with n >= 2 carry no action of type (A)
distinct_from:
  type-a-actors-have-no-proper-power-cyclic-edge-splittings: that excludes type (A) actions through irreducible tree actions, so it needs the absence of an invariant end; BS(1,n) is an ascending HNN extension, its Bass-Serre tree has a G-invariant end, and this is exactly the case that obstruction leaves open.
  type-a-actors-have-no-infinite-virtually-central-subgroup: that excludes actors with an infinite virtually central subgroup, such as BS(m,m); BS(1,n) with n >= 2 has no infinite virtually central subgroup, so that obstruction says nothing here either.
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that embeds BS(1,n) in a finitely presented simple group through some type (A) overgroup; this asks whether BS(1,n) is its own type (A) actor, which is strictly stronger and is what the proper-power route claims to settle.
---

**OPEN.**

## Statement

Let `n >= 2` and `BS(1,n) = <a, t | t a t^{-1} = a^n>`. Then `BS(1,n)` carries no
action of type (A): no faithful action on a set `X` with finitely generated point
stabilizers and finitely many orbits of two-element subsets.

## Why the existing obstructions miss it

This is the exact case left over by
`type-a-actors-have-no-proper-power-cyclic-edge-splittings`, whose advertised
statement ("BS(m,n) with |m| != |n| carry no type (A) action") reaches only
`|m|, |n| >= 2`.

- **The proper-power route needs irreducibility.** Its hypothesis is an
  irreducible tree action: minimal, without inversions, without a fixed vertex,
  **and without an invariant end**. The Bass-Serre tree of an ascending HNN
  extension has a `G`-invariant end, so the hypothesis fails and part (b) of that
  claim does not apply. Step 3 of
  `type-a-actors-split-only-over-orbit-finite-edges-proof` (the unbounded case) is
  discharged only by uniqueness of the end with property (P), so it has nothing to
  say once an invariant end exists; the route uses no other property separating
  ascending from non-ascending splittings.
- **The virtually central obstruction misses it.** `BS(1,n)` with `n >= 2` is
  non-unimodular and has no infinite virtually central subgroup, so
  `type-a-actors-have-no-infinite-virtually-central-subgroup` does not exclude it.
- **No other obstruction in the graph covers it.** `BS(1,n)` is one-ended and
  solvable, so the finite-edge instance and the ends argument do not reach it.

## What would settle it

Either an obstruction that survives an invariant end — a replacement for the
uniqueness-of-end step that does not assume irreducibility — or an explicit type (A)
action of `BS(1,n)`, which would refute this claim and cap the proper-power theorem
at `|m|, |n| >= 2` permanently.

## Attempts

- 2026-09-18 (referee pass on `type-a-actors-have-no-proper-power-cyclic-edge-splittings`):
  recorded as the gap. No attempt yet.
